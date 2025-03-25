---
authors:
  - maxime
title: "Control flow analysis with hax"
date: 2025-03-25
---

# Control flow analysis
A difficulty of formal verification is that specifying programs can be hard. Certain kinds of programs can end up having a specification that is as complex as the code itself. In this case it is usually better to focus on simpler properties rather than a full specification. For example, showing that before calling one function you always  call another function (imagine a validation function). This is what we call control flow analysis, and hax can be used to prove this kind of properties of Rust programs.
## Example: validating data before adding it to a state
Let's take a simple example, we have a program that receives messages and stores them in a state, but it needs to check that a message is valid before storing it. Here is a Rust example of this:
```rust
struct State(Vec<String>);

enum Error {
    InvalidMessage
}

fn validate_message(msg: &str) -> Result<(), Error> {
    if msg == "" {
        Err(Error::InvalidMessage)
    } else {
        Ok(())
    }
}

impl State {
    fn commit_message(&mut self, msg: String) {
        self.0.push(msg)
    }

    fn receive_message(&mut self, msg: String)-> Result<(), Error> {
        validate_message(&msg)?;
        self.commit_message(msg);
        Ok(())
    }
}
```
## Showing that all committed messages have been validated
An interesting property would be to show that `validate_message` is always called before `commit_message`. Let's make a specification for this using hax:
```rust
#[hax_lib::fstar::before(r"
assume val message_validated: string -> Type0
")]
#[hax_lib::opaque]
#[hax_lib::ensures(|_| fstar!("message_validated $msg"))]
fn validate_message(msg: &str) -> Result<(), Error> {
    if msg == "" {
        Err(Error::InvalidMessage)
    } else {
        Ok(())
    }
}

#[hax_lib::attributes]
impl State {
    #[hax_lib::requires(fstar!("message_validated $msg"))]
    fn commit_message(&mut self, msg: String) {
        self.0.push(msg)
    }

    fn receive_message(&mut self, msg: String)-> Result<(), Error> {
        validate_message(&msg)?;
        self.commit_message(msg);
        Ok(())
    }
}
```
Here we define `message_validated` as an abstract predicate, and we add a post-condition on `validate_message` to specify that this predicate holds if and only if `validate_message` has been called on the message. Then we can add a precondition on `commit_message` so that it is now mandatory to have called `validate_message` before `commit_message`. You can try [this example](https://hax-playground.cryspen.com/#fstar/4dec0f8ea9/gist=8f4ff24a1e2ecd1a0e45716e2a1f6c5d) in the hax playground, extract to F* and type-check. F* type-checking succeeds which means we have proven that whenever `commit_message` is called, `validate_message` has been called before on the same message.
## Showing that all valid messages are committed
The property we showed in the previous section is a safety property: we show that we cannot end in a bad state by committing a message that has not been validated. But this doesn't mean we actually commit any message. Let's modify our specification to show that we do commit messages:
```rust
#[hax_lib::fstar::before(r"
assume val message_validated: string -> Type0
assume val message_committed: string -> Type0
")]
#[hax_lib::opaque]
#[hax_lib::ensures(|_| fstar!("message_validated $msg"))]
fn validate_message(msg: &str) -> Result<(), Error> {
    if msg == "" {
        Err(Error::InvalidMessage)
    } else {
        Ok(())
    }
}

#[hax_lib::attributes]
impl State {
    #[hax_lib::requires(fstar!("message_validated $msg"))]
    #[hax_lib::opaque]
    #[hax_lib::ensures(|_| fstar!("message_committed $msg"))]
    fn commit_message(&mut self, msg: String) {
        self.0.push(msg)
    }

    #[hax_lib::ensures(|res| fstar!("message_committed $msg"))]
    fn receive_message(&mut self, msg: String)-> Result<(), Error> {
        validate_message(&msg)?;
        self.commit_message(msg);
        Ok(())
    }
}
```
We added a new abstract predicate `message_committed` that holds if a message has been committed. With this specification, F* is not able to prove the post-condition for `receive_message`. Of course, the message is committed only when it is valid so we need to add this condition in our post-condition:
```rust
#[hax_lib::ensures(|res| hax_lib::implies(validate_message(&msg).is_ok(), fstar!("message_committed $msg")))]
fn receive_message(&mut self, msg: String)-> Result<(), Error> {
    validate_message(&msg)?;
    self.commit_message(msg);
    Ok(())
}
```
You can [try this in the hax playground](https://hax-playground.cryspen.com/#fstar/4dec0f8ea9/gist=bdf9aa71a0c94a0318bc1682dd03d2a4) and see that F* is able to prove this post-condition!
## Verifying sandwich
In [collaboration](https://cryspen.com/post/hax-sandbox/) with SandboxAQ, we worked on verifying the [sandwich](https://github.com/sandbox-quantum/sandwich) library. Sandwich is a Rust high-level cryptographic library that wraps around lower-level libraries like OpenSSL. OpenSSL is a C library and sandwich interfaces with it using Rust/C bindings which means it was impossible for us to push verification to the lowest level because of raw pointers that are not supported by hax. Instead, we focused on more abstract properties about the OpenSSL API functions that need to be called (in the right order, with the right parameters) to make sure encryption is correctly set. We used the methodology presented above to prove these properties, see [this blogpost for more information](todo-link).
