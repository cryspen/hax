# `hax-types`
This crate contains the type definitions that are used to communicate between:
 - the command line (the `cargo-hax` binary);
 - the custom rustc driver;
 - the hax engine (the `hax-engine` binary).
 
Those three components exchange JSON messages: the CLI drives the
engine over its stdin and stdout, and the driver writes `haxmeta`
files to the target directory, announcing them as JSON lines on its
stderr.
