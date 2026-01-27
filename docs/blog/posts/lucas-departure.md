---
authors:
  - lucas
title: "My Departure from hax and Cryspen"
date: 2026-01-14
---

Today, I want to share an update on both my professional path and my role in
hax. I decided to leave Cryspen, and as a result, I will also be stepping away
from hax.

## Looking Back

Back in September 2023, while I was working at Inria, I started working with
Karthikeyan on [Hacspec](https://github.com/hacspec/hacspec). Hacspec was
a domain-specific language embedded in Rust's syntax, aimed at cryptography
specification and verification. It relied on the surface AST (abstract syntax
tree) of the Rust compiler (rustc). Using such an early representation in the
compiler pipeline gave us very limited information: no types, no name resolution
-- essentially just syntax.

Both technically and in terms of intent, Hacspec had limitations. In December
2023, we decided to take a fresh start and build a new tool from the ground
up: hax.

Designing and implementing hax has been a fun adventure. I had the constraint to
write the "compiler" part of hax in OCaml. That led me to design hax in two main
parts:

 - **The frontend**: hooks into rustc and dumps enhanced ASTs, inlining a large
   amount of semantic information about Rust programs. The frontend produces a
   comprehensive, complete, and easy-to-consume AST that other tools can build
   upon. It grew a lot, notably thanks to our collaboration with Inria (for
   Charon and Aeneas), and especially thanks to
   [Nadrieril](https://github.com/Nadrieril), with whom it has been a great
   pleasure and a lot of fun to work.

 - **The engine**: an OCaml binary that reads our frontend's Rust AST, applies a
   sequence of translation phases, and finally outputs F*, Coq, etc.

For a full year at Inria and then two years at Cryspen, I was the main developer
of hax. Throughout this time, I greatly enjoyed working with Karthik; we
discussed many aspects of hax countless times: its design, its applications, the
workflows, and more. Those were great conversations, essential to the
development of hax.

Leading the development of hax was a great and intense experience. I had to engineer a
pretty large piece of software, design interesting semantic compiler passes,
build debugging tools, do DevOps work, build a playground, and more. I also
learned how complicated human interactions can be.

## Working at Cryspen

During my time at Cryspen, the proofs and tools team grew a lot. When I arrived,
it was Karthik and me. Then [Maxime](https://cryspen.com/post/welcome_maxime/)
joined towards the end of my first year (in August 2024). In May the next year
[Clément](https://cryspen.com/post/welcome_clement/) arrived, and very recently,
in November 2025, [Alex](https://cryspen.com/post/welcome_alex/) arrived. I
really enjoyed working with everyone in the proofs and tools team at Cryspen!

Beyond the proofs and tools team, it was also great to work with others at Cryspen:
Jan, Jonas, Clara.

## The Future

After three years working on hax, I decided it was time for me to leave. Hax is
a bit my baby, so that was a very hard decision to make.

That said, the rest of the proofs and tools team at Cryspen will continue
maintaining, improving, and applying hax to cool real-world Rust projects! They
are already working on the new Lean backend, on better libraries, and on very
exciting applications!

I'm proud of what hax has become, and I hope it will have a bright future! If
hax speaks to you, consider following the project, trying it out, or
contributing.
