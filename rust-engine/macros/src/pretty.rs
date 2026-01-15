#[derive(Debug, PartialEq, Clone, Debug)]
pub enum Node {
    /// Plain text
    Verbatim(String),
    /// Group
    Group {
        verb: Option<String>,
        n: Option<usize>,
        args: Vec<Node>,
    },
    Concat(Box<Node>, Box<Node>),
}

#[derive(Clone, Debug)]
pub enum Token {
    Start {
        verb: Option<String>,
        n: Option<usize>,
    },
    End,
    Verbatim(String),
    Command(String),
}

impl Token {
    fn to_string(&self, config: &TokenizerConfig) -> String {
        match self {
            Token::Start {
                verb: Some(verb),
                n: Some(n),
            } => format!(
                "{}{verb}[{n}]{}",
                &config.verb_prefix, &config.left_group_delimiter
            ),
            Token::Start {
                verb: Some(verb),
                n: None,
            } => format!(
                "{}{verb}{}",
                &config.verb_prefix, &config.left_group_delimiter
            ),
            Token::Start {
                verb: None,
                n: None,
            } => format!("{}", &config.left_group_delimiter),
            Token::Start { .. } => panic!("malformed start"),
            Token::End => format!("{}", &config.right_group_delimiter),
            Token::Verbatim(s) => s.clone(),
            Token::Command(c) => format!("{}{c}", &config.verb_prefix),
        }
    }
}

impl Node {
    fn concat(&self, rhs: Self) -> Self {
        Self::Concat(Box::new(self.clone()), Box::new(rhs))
    }
}

fn parse(tokens: &[Token]) -> Node {
    let level = 0;
    let mut stack = vec![Node::Verbatim("".to_string())];
    for token in tokens {
        match token {
            Token::Start { verb, n } => todo!(),
            Token::End => {
                let last = stack.pop();
            }
            Token::Verbatim(s) => {
                let last = stack.first_mut().unwrap();
                *last = last.concat(Node::Verbatim(s.to_string()));
            }
            Token::Command(c) => {
                let last = stack.first_mut().unwrap();
                *last = last.concat(Node::Group {
                    verb: Some(c.to_string()),
                    n: None,
                    args: vec![],
                });
            }
        }
    }
    stack.last().unwrap()
}

use regex::*;

struct TokenizerConfig {
    left_group_delimiter: String,
    right_group_delimiter: String,
    verb_prefix: String,
    verbs: Vec<Verb>,
}

struct Verb {
    name: String,
    int_parameter: bool,
    arity: u8,
}

impl Verb {
    fn new(name: &str, arity: u8) -> Verb {
        Verb {
            name: name.to_string(),
            int_parameter: false,
            arity,
        }
    }
    fn to_start_re(&self) -> String {
        let verb = regex::escape(&self.name);
        format!(
            "(?<verb>{verb}){}",
            if self.int_parameter {
                r"\[(?<n>\d+)\]"
            } else {
                ""
            }
        )
    }
}
impl TokenizerConfig {
    fn tokenize(&self, input: &str) -> Vec<Token> {
        let verbs = self
            .verbs
            .iter()
            .filter(|verb| verb.arity > 0)
            .map(Verb::to_start_re)
            .collect::<Vec<_>>()
            .join("|");
        let verb_prefix = regex::escape(&self.verb_prefix);
        let verb_arity0 = self
            .verbs
            .iter()
            .filter(|verb| verb.arity == 0)
            .map(|verb| format!("{verb_prefix}(?<verb0>{})", regex::escape(&verb.name)))
            .collect::<Vec<_>>()
            .join("|");
        let left_group_delimiter = regex::escape(&self.left_group_delimiter);
        let right_group_delimiter = regex::escape(&self.right_group_delimiter);
        let re_begin = format!(r"({verb_prefix}({verbs}))?(?<start>{left_group_delimiter})");
        let re_end = format!("(?<end>{right_group_delimiter})");
        let re_escapes = {
            let disj = vec![
                &self.left_group_delimiter[0..1],
                &self.right_group_delimiter[0..1],
                &self.verb_prefix[0..1],
            ]
            .iter()
            .map(|s| format!("{}{s}", "\\"))
            .map(|s| regex::escape(&s))
            .collect::<Vec<_>>()
            .join("|");
            format!("(?<escape>({disj}))")
        };
        let re = Regex::new(&format!("{re_escapes}|{verb_arity0}|{re_begin}|{re_end}")).unwrap();
        let mut cursor = 0;
        let mut tokens = vec![];
        for capture in re.captures_iter(input) {
            let whole = capture.get(0).unwrap();
            let verbatim = input[cursor..whole.start()].to_string();
            if !verbatim.is_empty() {
                tokens.push(Token::Verbatim(verbatim));
            }
            if capture.name("start").is_some() {
                let verb = capture.name("verb").map(|m| m.as_str().to_string());
                let n = capture.name("n").map(|m| str::parse(m.as_str()).unwrap());
                tokens.push(Token::Start { verb, n });
            } else if capture.name("end").is_some() {
                tokens.push(Token::End);
            } else if capture.name("escape").is_some() {
                tokens.push(Token::Verbatim(whole.as_str()[1..].to_string()));
            } else if capture.name("verb0").is_some() {
                tokens.push(Token::Command(
                    capture.name("verb0").unwrap().as_str().to_string(),
                ));
            } else {
                panic!()
            }
            cursor = whole.end();
        }
        let verbatim = input[cursor..].to_string();
        if !verbatim.is_empty() {
            tokens.push(Token::Verbatim(verbatim));
        }
        tokens
    }
}

#[test]
fn test() {
    let input = "a{{hel{{lo}} + 3}} b * @nest[2]{{hello}}";
    let config = TokenizerConfig {
        left_group_delimiter: "{{".into(),
        right_group_delimiter: "}}".into(),
        verb_prefix: "@".into(),
        verbs: vec![
            Verb {
                name: "nest".into(),
                int_parameter: true,
                arity: 1,
            },
            Verb::new("n", 0),
            Verb::new("hardline", 0),
            Verb::new("l", 0),
            Verb::new("softline", 0),
            Verb::new("L", 0),
            Verb::new("line", 0),
            Verb::new("intersperse", 2),
        ],
    };
    let result = config.tokenize(input);
    println!("{:#?}", result);
}
