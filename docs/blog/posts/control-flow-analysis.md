---
authors:
  - maxime
title: "Control flow analysis with hax"
date: 2025-03-25
---

# Control flow analysis
A difficulty of formal verification is that specifying programs can be hard. Certain kinds of programs can end up having a specification that is as complex as the code itself. In this case it is usually better to focus on simple but more interesting and understandable properties rather than an equivalence proof with a full specification. For example, showing that before calling one function you always call another function (imagine a validation function). Indeed, forgetting a validation step can lead to severe vulnerabilities (see [this example](https://nvd.nist.gov/vuln/detail/cve-2014-1266) of a vulnerability because of a missing signature check). This is what we call control flow analysis, and hax can be used to prove this kind of properties of Rust programs. Control flow properties come up in various project of interest to Cryspen, including protocols like [MLS](https://github.com/openmls/openmls), APIs like [sandwich](https://github.com/sandbox-quantum/sandwich) and even web services that need to sanitize SQL queries. 
## Example: validating data before adding it to a state
Let's look at a simple example. A program receives messages and stores them in a state, but it needs to check that a message is valid before storing it. Here is a Rust example of this:
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
    fn store_message(&mut self, msg: String) {
        self.0.push(msg)
    }

    fn receive_message(&mut self, msg: String)-> Result<(), Error> {
        validate_message(&msg)?;
        self.store_message(msg);
        Ok(())
    }
}
```
## Showing that all stored messages have been validated
The validation requirement here is that `validate_message` must always be called before `store_message`. Let's make a specification for this using hax:
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
    fn store_message(&mut self, msg: String) {
        self.0.push(msg)
    }

    fn receive_message(&mut self, msg: String)-> Result<(), Error> {
        validate_message(&msg)?;
        self.store_message(msg);
        Ok(())
    }
}
```
Here we define `message_validated` as an abstract predicate, and we add a post-condition on `validate_message` to specify that this predicate holds if and only if `validate_message` has been called on the message. Then we can add a precondition on `store_message` so that it is now mandatory to have called `validate_message` before `store_message`. You can try [this example](https://hax-playground.cryspen.com/#fstar/4dec0f8ea9/gist=5b71b874a098f024c6ee4c6610185bab) in the hax playground, extract to F* and type-check. F* type-checking succeeds which means we have proven that whenever `store_message` is called, `validate_message` has been called before on the same message.
## Showing that all valid messages are stored
The property we showed in the previous section is a safety property: we show that we cannot end in a bad state by storing a message that has not been validated. But this doesn't mean we actually store any message. Let's extend our specification to ensure that we *do* store messages:
```rust
#[hax_lib::fstar::before(r"
assume val message_validated: string -> Type0
assume val message_stored: string -> Type0
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
    #[hax_lib::ensures(|_| fstar!("message_stored $msg"))]
    fn store_message(&mut self, msg: String) {
        self.0.push(msg)
    }

    #[hax_lib::ensures(|res| fstar!("message_stored $msg"))]
    fn receive_message(&mut self, msg: String)-> Result<(), Error> {
        validate_message(&msg)?;
        self.store_message(msg);
        Ok(())
    }
}
```
We added a new abstract predicate `message_stored` that holds if a message has been stored. With this specification, F* is not able to prove the post-condition for `receive_message`. Of course, the message is stored only when it is valid. We need to add this to our post-condition:
```rust
#[hax_lib::ensures(|res| hax_lib::implies(validate_message(&msg).is_ok(), fstar!("message_stored $msg")))]
fn receive_message(&mut self, msg: String)-> Result<(), Error> {
    validate_message(&msg)?;
    self.store_message(msg);
    Ok(())
}
```
You can [try this in the hax playground](https://hax-playground.cryspen.com/#fstar/4dec0f8ea9/gist=c34844cf9bb3ae382368153c7bf5493c) and see that F* is able to prove this post-condition!
## Verifying sandwich
In [collaboration](https://cryspen.com/post/hax-sandbox/) with SandboxAQ, we worked on verifying the [sandwich](https://github.com/sandbox-quantum/sandwich) library. Sandwich is a Rust high-level cryptographic library that wraps around lower-level libraries like OpenSSL. OpenSSL is a C library and sandwich interfaces with it using Rust/C bindings. We analyzed the code starting from the public Sandwich API all the way down to the Rust wrappers around OpenSSL C calls. We focused on properties about the OpenSSL API functions that need to be called (in the right order, with the right parameters) to make sure encryption is correctly set. We used the methodology presented above to prove these properties, see [this blogpost for more information](todo-link).
