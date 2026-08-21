//! Model of `core::fmt`.
//!
//! Formatting *produces text*, and this model deliberately does not: the model's
//! [`Formatter`] carries the formatting options but no output buffer, so every
//! writing operation ([`Formatter::write_str`], [`Formatter::pad`], the `Debug*`
//! builders, the [`Display`]/[`Debug`] impls, …) succeeds without producing
//! anything. Rendering the output would need a `str` model this crate does not
//! have (see `core::str`, and `rust_primitives::string`'s four arena helpers).
//!
//! What *is* faithful here is the API surface plus the parts that are pure data:
//! the formatting traits downstream code puts in its bounds, and the
//! [`FormattingOptions`] / [`Formatter`] query methods, whose values round-trip
//! exactly as in real `core`.
#![allow(unused_variables)]

use crate::option::Option;

/// See [`std::fmt::Error`]
#[cfg_attr(test, derive(PartialEq, Debug))]
pub struct Error;

/// See [`std::fmt::Result`]
pub type Result = super::result::Result<(), Error>;

/// See [`std::fmt::Formatter`]
///
/// Real `core`'s `Formatter<'a>` also holds the `&'a mut dyn Write` it renders
/// into. The model drops it — nothing is ever rendered (see the module docs) —
/// and keeps only the options, which is what the query methods below observe.
pub struct Formatter {
    formatting_options: FormattingOptions,
}

// Not a `core` item: [`Formatter::flags`] needs it because Aeneas fails to
// translate a function that branches on several `bool` fields of `self` and
// accumulates into a local ("Unreachable"); with the branch behind a call, it
// translates fine.
fn flag_bit(set: bool, value: core::primitive::u32) -> core::primitive::u32 {
    if set { value } else { 0 }
}

impl Formatter {
    /// See [`std::fmt::Formatter::new`]
    ///
    /// The writer is ignored. It is also generic rather than `dyn Write`: `dyn`
    /// has no counterpart in the F* proof libraries.
    pub fn new<W: Write>(write: &mut W, options: FormattingOptions) -> Formatter {
        Formatter {
            formatting_options: options,
        }
    }

    /// See [`std::fmt::Formatter::with_options`]
    pub fn with_options(&mut self, options: FormattingOptions) -> Formatter {
        Formatter {
            formatting_options: options,
        }
    }

    /// See [`std::fmt::Formatter::options`]
    pub fn options(&self) -> FormattingOptions {
        // Spelled out field by field: the model cannot `derive(Copy)`, because
        // `marker::Copy` is blanket-implemented under `--cfg hax`.
        FormattingOptions {
            sign_plus: self.formatting_options.sign_plus,
            sign_minus: self.formatting_options.sign_minus,
            alternate_flag: self.formatting_options.alternate_flag,
            zero_pad_flag: self.formatting_options.zero_pad_flag,
            debug_lower_hex: self.formatting_options.debug_lower_hex,
            debug_upper_hex: self.formatting_options.debug_upper_hex,
            fill_char: self.formatting_options.fill_char,
            align_code: self.formatting_options.align_code,
            width_value: self.formatting_options.width_value,
            width_set: self.formatting_options.width_set,
            precision_value: self.formatting_options.precision_value,
            precision_set: self.formatting_options.precision_set,
        }
    }

    /// See [`std::fmt::Formatter::write_str`]
    pub fn write_str(&mut self, data: &str) -> Result {
        Result::Ok(())
    }

    /// See [`std::fmt::Formatter::write_fmt`]
    ///
    /// Unlike [`write`] on a caller-provided sink, there is nothing to forward
    /// to here: the model's `Formatter` has no sink.
    ///
    /// The parameter real `core` calls `fmt` is `args` here: a binder named after
    /// a module shadows it in the extracted Lean, and `fmt.Error` in this
    /// signature would then elaborate as a field projection on the binder.
    pub fn write_fmt(&mut self, args: Arguments) -> Result {
        Result::Ok(())
    }

    /// See [`std::fmt::Formatter::pad`]
    ///
    /// Real `core` truncates `s` to the precision and pads it to the width; the
    /// model has nowhere to put the result, so it writes nothing.
    pub fn pad(&mut self, s: &str) -> Result {
        Result::Ok(())
    }

    /// See [`std::fmt::Formatter::pad_integral`]
    ///
    /// Writes nothing, for the same reason as [`Formatter::pad`].
    pub fn pad_integral(&mut self, is_nonnegative: bool, prefix: &str, buf: &str) -> Result {
        Result::Ok(())
    }

    /// See [`std::fmt::Formatter::flags`]
    ///
    /// The six flag bits real `core` keeps at bits 21..27 of its packed `flags`
    /// field, shifted down to 0..6 — exactly what real `core` returns.
    pub fn flags(&self) -> core::primitive::u32 {
        flag_bit(self.formatting_options.sign_plus, 1)
            + flag_bit(self.formatting_options.sign_minus, 2)
            + flag_bit(self.formatting_options.alternate_flag, 4)
            + flag_bit(self.formatting_options.zero_pad_flag, 8)
            + flag_bit(self.formatting_options.debug_lower_hex, 16)
            + flag_bit(self.formatting_options.debug_upper_hex, 32)
    }

    /// See [`std::fmt::Formatter::fill`]
    pub fn fill(&self) -> char {
        self.formatting_options.fill_char
    }

    /// See [`std::fmt::Formatter::align`]
    pub fn align(&self) -> Option<Alignment> {
        self.formatting_options.get_align()
    }

    /// See [`std::fmt::Formatter::width`]
    pub fn width(&self) -> Option<core::primitive::usize> {
        match self.formatting_options.get_width() {
            Option::Some(width) => Option::Some(width as core::primitive::usize),
            Option::None => Option::None,
        }
    }

    /// See [`std::fmt::Formatter::precision`]
    pub fn precision(&self) -> Option<core::primitive::usize> {
        match self.formatting_options.get_precision() {
            Option::Some(precision) => Option::Some(precision as core::primitive::usize),
            Option::None => Option::None,
        }
    }

    /// See [`std::fmt::Formatter::sign_plus`]
    pub fn sign_plus(&self) -> bool {
        self.formatting_options.sign_plus
    }

    /// See [`std::fmt::Formatter::sign_minus`]
    pub fn sign_minus(&self) -> bool {
        self.formatting_options.sign_minus
    }

    /// See [`std::fmt::Formatter::alternate`]
    pub fn alternate(&self) -> bool {
        self.formatting_options.alternate_flag
    }

    /// See [`std::fmt::Formatter::sign_aware_zero_pad`]
    pub fn sign_aware_zero_pad(&self) -> bool {
        self.formatting_options.zero_pad_flag
    }

    /// See [`std::fmt::Formatter::sign`]
    pub fn sign(&self) -> Option<Sign> {
        self.formatting_options.get_sign()
    }

    /// See [`std::fmt::Formatter::debug_struct`]
    pub fn debug_struct(&mut self, name: &str) -> DebugStruct {
        DebugStruct
    }

    /// See [`std::fmt::Formatter::debug_tuple`]
    pub fn debug_tuple(&mut self, name: &str) -> DebugTuple {
        DebugTuple
    }

    /// See [`std::fmt::Formatter::debug_list`]
    pub fn debug_list(&mut self) -> DebugList {
        DebugList
    }

    /// See [`std::fmt::Formatter::debug_set`]
    pub fn debug_set(&mut self) -> DebugSet {
        DebugSet
    }

    /// See [`std::fmt::Formatter::debug_map`]
    pub fn debug_map(&mut self) -> DebugMap {
        DebugMap { has_key: false }
    }
}

/// See [`std::fmt::Display`]
pub trait Display {
    /// See [`std::fmt::Display::fmt`]
    fn fmt(&self, f: &mut Formatter) -> Result;
}

/// See [`std::fmt::Debug`]
pub trait Debug {
    /// See [`std::fmt::Debug::fmt`]
    #[cfg(not(hax_backend_fstar))]
    fn fmt(&self, f: &mut Formatter) -> Result;
    #[cfg(hax_backend_fstar)]
    fn dbg_fmt(&self, f: &mut Formatter) -> Result;
}

/// See [`std::fmt::Arguments`]
//
// The field is a placeholder — the model does not track format arguments. It is
// `pub` only so that other modules' tests can build one to pass to the
// `Arguments`-taking functions in `crate::panicking`.
///
/// The only thing the model records is the "no placeholders" case
/// (`format_args!("a literal")`), which is what [`Arguments::as_str`] observes.
/// Everything else is built by the opaque constructors in [`rt`] and carries no
/// information.
///
/// The type itself extracts, but Aeneas cannot translate a function that stores
/// a `&'static str` into a struct or reads one back out, so the two functions
/// that touch the payload — and [`write`], which calls `as_str` — are dropped
/// from the Lean extraction.
pub struct Arguments<'a>(Option<&'static str>, std::marker::PhantomData<&'a ()>);

impl<T> Debug for T {
    #[cfg(not(hax_backend_fstar))]
    fn fmt(&self, f: &mut Formatter) -> Result {
        Result::Ok(())
    }
    #[cfg(hax_backend_fstar)]
    fn dbg_fmt(&self, f: &mut Formatter) -> Result {
        Result::Ok(())
    }
}

// No blanket `Display` (unlike `Debug` above); spell out the integer impls,
// stubbed to `Ok(())` like the rest of this module.
macro_rules! impl_display_for_int {
    ($($t:ty),*) => {
        $(
            impl Display for $t {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    Result::Ok(())
                }
            }
        )*
    };
}

impl_display_for_int!(
    core::primitive::u8,
    core::primitive::u16,
    core::primitive::u32,
    core::primitive::u64,
    core::primitive::u128,
    core::primitive::usize,
    core::primitive::i8,
    core::primitive::i16,
    core::primitive::i32,
    core::primitive::i64,
    core::primitive::i128,
    core::primitive::isize
);

// The ten empty impl blocks below are padding: hax numbers the anonymous impls
// of a module in source order, and the `write_fmt` in the eleventh block has to
// land on the index real `core` gives `Formatter::write_fmt` for the generated
// F* name to match what downstream extractions reference
// (`Core_models.Fmt.impl_12__write_fmt`). Do not insert impl blocks before this
// point, and do not renumber them. `Formatter::write_fmt` above is the same
// function under its proper name.
impl<'a> Arguments<'a> {}
impl<'a> Arguments<'a> {}
impl<'a> Arguments<'a> {}
impl<'a> Arguments<'a> {}
impl<'a> Arguments<'a> {}
impl<'a> Arguments<'a> {}
impl<'a> Arguments<'a> {}
impl<'a> Arguments<'a> {}
impl<'a> Arguments<'a> {}
impl<'a> Arguments<'a> {}
impl<'a> Arguments<'a> {
    fn write_fmt(f: &mut Formatter, args: Arguments) -> Result {
        Result::Ok(())
    }

    /// See [`std::fmt::Arguments::from_str`]
    #[cfg_attr(charon, aeneas::exclude)]
    pub fn from_str(s: &'static str) -> Arguments<'a> {
        Arguments(Option::Some(s), std::marker::PhantomData)
    }

    /// See [`std::fmt::Arguments::as_str`]
    // Excluded from coverage: `from_str` is the only constructor, so the `None`
    // arm — real `core`'s "has placeholders" case, which this model cannot
    // represent — is unconstructible.
    #[cfg_attr(coverage_nightly, coverage(off))]
    #[cfg_attr(charon, aeneas::exclude)]
    pub fn as_str(&self) -> Option<&'static str> {
        match &self.0 {
            Option::Some(s) => Option::Some(*s),
            Option::None => Option::None,
        }
    }
}

// -----------------------------------------------------------------------------
// Formatting options
// -----------------------------------------------------------------------------

/// See [`std::fmt::Alignment`]
#[cfg_attr(test, derive(PartialEq, Debug))]
pub enum Alignment {
    /// See [`std::fmt::Alignment::Left`]
    Left,
    /// See [`std::fmt::Alignment::Right`]
    Right,
    /// See [`std::fmt::Alignment::Center`]
    Center,
}

/// See [`std::fmt::Sign`]
#[cfg_attr(test, derive(PartialEq, Debug))]
pub enum Sign {
    /// See [`std::fmt::Sign::Plus`]
    Plus,
    /// See [`std::fmt::Sign::Minus`]
    Minus,
}

/// See [`std::fmt::DebugAsHex`]
#[cfg_attr(test, derive(PartialEq, Debug))]
pub enum DebugAsHex {
    /// See [`std::fmt::DebugAsHex::Lower`]
    Lower,
    /// See [`std::fmt::DebugAsHex::Upper`]
    Upper,
}

/// See [`std::fmt::FormattingOptions`]
///
/// Real `core` packs the flags, the fill character, the width and the precision
/// into a `u32` plus two `u16`s. The model keeps the very same information in
/// named fields of primitive type: the getters then transcribe real `core`'s
/// bodies without bit twiddling, and the options can be copied by listing their
/// fields (the model cannot `derive(Copy)`, see [`Formatter::options`]).
///
/// None of the field names may coincide with a method name of this type — the
/// setters are `width`, `fill`, `align`, … — because Lean derives a projection
/// `FormattingOptions.width` from the field and Aeneas resolves the clash by
/// renaming the *method* to `FormattingOptions.impl.width`. An extracted client
/// calling the setter asks for the unrenamed name and gets the projection. Hence
/// `width_value`, `fill_char`, `align_code`, … here. Same for
/// [`Formatter`]'s single field against [`Formatter::options`].
pub struct FormattingOptions {
    sign_plus: bool,
    sign_minus: bool,
    alternate_flag: bool,
    zero_pad_flag: bool,
    debug_lower_hex: bool,
    debug_upper_hex: bool,
    fill_char: char,
    /// The alignment, in real `core`'s encoding: `0` left, `1` right, `2`
    /// center, `3` unset.
    align_code: core::primitive::u8,
    width_value: core::primitive::u16,
    width_set: bool,
    precision_value: core::primitive::u16,
    precision_set: bool,
}

// The setters keep real `core`'s chaining signature, `&mut self -> &mut Self`,
// which hax's F* backend cannot represent: a `&mut` outside a parameter position
// is rejected outright (HAX0003, hacspec/hax#420), and `#[hax_lib::opaque]` does
// not help since it is the *signature* that is unrepresentable. So they are
// dropped from the F* extraction only; Aeneas takes them as written.
impl FormattingOptions {
    /// See [`std::fmt::FormattingOptions::new`]
    pub fn new() -> FormattingOptions {
        FormattingOptions {
            sign_plus: false,
            sign_minus: false,
            alternate_flag: false,
            zero_pad_flag: false,
            debug_lower_hex: false,
            debug_upper_hex: false,
            fill_char: ' ',
            align_code: 3,
            width_value: 0,
            width_set: false,
            precision_value: 0,
            precision_set: false,
        }
    }

    /// See [`std::fmt::FormattingOptions::sign`]
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn sign(&mut self, sign: Option<Sign>) -> &mut Self {
        let (plus, minus) = match sign {
            Option::Some(Sign::Plus) => (true, false),
            Option::Some(Sign::Minus) => (false, true),
            Option::None => (false, false),
        };
        self.sign_plus = plus;
        self.sign_minus = minus;
        self
    }

    /// See [`std::fmt::FormattingOptions::sign_aware_zero_pad`]
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn sign_aware_zero_pad(&mut self, sign_aware_zero_pad: bool) -> &mut Self {
        self.zero_pad_flag = sign_aware_zero_pad;
        self
    }

    /// See [`std::fmt::FormattingOptions::alternate`]
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn alternate(&mut self, alternate: bool) -> &mut Self {
        self.alternate_flag = alternate;
        self
    }

    /// See [`std::fmt::FormattingOptions::fill`]
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn fill(&mut self, fill: char) -> &mut Self {
        self.fill_char = fill;
        self
    }

    /// See [`std::fmt::FormattingOptions::align`]
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn align(&mut self, align: Option<Alignment>) -> &mut Self {
        self.align_code = match align {
            Option::Some(Alignment::Left) => 0,
            Option::Some(Alignment::Right) => 1,
            Option::Some(Alignment::Center) => 2,
            Option::None => 3,
        };
        self
    }

    /// See [`std::fmt::FormattingOptions::width`]
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn width(&mut self, width: Option<core::primitive::u16>) -> &mut Self {
        match width {
            Option::Some(width) => {
                self.width_set = true;
                self.width_value = width;
            }
            Option::None => {
                self.width_set = false;
                self.width_value = 0;
            }
        }
        self
    }

    /// See [`std::fmt::FormattingOptions::precision`]
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn precision(&mut self, precision: Option<core::primitive::u16>) -> &mut Self {
        match precision {
            Option::Some(precision) => {
                self.precision_set = true;
                self.precision_value = precision;
            }
            Option::None => {
                self.precision_set = false;
                self.precision_value = 0;
            }
        }
        self
    }

    /// See [`std::fmt::FormattingOptions::debug_as_hex`]
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn debug_as_hex(&mut self, debug_as_hex: Option<DebugAsHex>) -> &mut Self {
        let (lower, upper) = match debug_as_hex {
            Option::Some(DebugAsHex::Lower) => (true, false),
            Option::Some(DebugAsHex::Upper) => (false, true),
            Option::None => (false, false),
        };
        self.debug_lower_hex = lower;
        self.debug_upper_hex = upper;
        self
    }

    /// See [`std::fmt::FormattingOptions::get_sign`]
    pub fn get_sign(&self) -> Option<Sign> {
        if self.sign_plus {
            Option::Some(Sign::Plus)
        } else if self.sign_minus {
            Option::Some(Sign::Minus)
        } else {
            Option::None
        }
    }

    /// See [`std::fmt::FormattingOptions::get_sign_aware_zero_pad`]
    pub fn get_sign_aware_zero_pad(&self) -> bool {
        self.zero_pad_flag
    }

    /// See [`std::fmt::FormattingOptions::get_alternate`]
    pub fn get_alternate(&self) -> bool {
        self.alternate_flag
    }

    /// See [`std::fmt::FormattingOptions::get_fill`]
    pub fn get_fill(&self) -> char {
        self.fill_char
    }

    /// See [`std::fmt::FormattingOptions::get_align`]
    pub fn get_align(&self) -> Option<Alignment> {
        match self.align_code {
            0 => Option::Some(Alignment::Left),
            1 => Option::Some(Alignment::Right),
            2 => Option::Some(Alignment::Center),
            _ => Option::None,
        }
    }

    /// See [`std::fmt::FormattingOptions::get_width`]
    pub fn get_width(&self) -> Option<core::primitive::u16> {
        if self.width_set {
            Option::Some(self.width_value)
        } else {
            Option::None
        }
    }

    /// See [`std::fmt::FormattingOptions::get_precision`]
    pub fn get_precision(&self) -> Option<core::primitive::u16> {
        if self.precision_set {
            Option::Some(self.precision_value)
        } else {
            Option::None
        }
    }

    /// See [`std::fmt::FormattingOptions::get_debug_as_hex`]
    pub fn get_debug_as_hex(&self) -> Option<DebugAsHex> {
        if self.debug_lower_hex {
            Option::Some(DebugAsHex::Lower)
        } else if self.debug_upper_hex {
            Option::Some(DebugAsHex::Upper)
        } else {
            Option::None
        }
    }

    /// See [`std::fmt::FormattingOptions::create_formatter`]
    ///
    /// The writer is ignored and generic, as in [`Formatter::new`].
    pub fn create_formatter<W: Write>(self, write: &mut W) -> Formatter {
        Formatter {
            formatting_options: self,
        }
    }
}

// -----------------------------------------------------------------------------
// Writing
// -----------------------------------------------------------------------------

/// See [`std::fmt::Write`]
pub trait Write {
    /// See [`std::fmt::Write::write_str`]
    fn write_str(&mut self, s: &str) -> Result;
}

/// `Write::write_char` and `Write::write_fmt` are trait *defaults* in real
/// `core`, which hax cannot express; like [`crate::cmp::Neq`] for
/// `PartialEq::ne`, they live in a blanket-implemented companion trait.
///
/// Excluded from the Lean extraction: `write_char` needs
/// `rust_primitives::string::str_of_char`, and the Lean side provides none of
/// the string primitives (`alloc::string` is excluded there for the same
/// reason).
#[cfg_attr(charon, aeneas::exclude)]
pub trait WriteDefaults {
    /// See [`std::fmt::Write::write_char`]
    fn write_char(&mut self, c: char) -> Result;
    /// See [`std::fmt::Write::write_fmt`]
    fn write_fmt(&mut self, args: Arguments) -> Result;
}

#[cfg_attr(charon, aeneas::exclude)]
impl<W: Write> WriteDefaults for W {
    fn write_char(&mut self, c: char) -> Result {
        self.write_str(rust_primitives::string::str_of_char(c))
    }
    fn write_fmt(&mut self, args: Arguments) -> Result {
        write(self, args)
    }
}

impl Write for Formatter {
    fn write_str(&mut self, s: &str) -> Result {
        Result::Ok(())
    }
}

/// See [`std::fmt::write`]
///
/// Real `core` renders the template and the arguments; the model can only
/// forward the literal case (see [`Arguments`]), and drops the rest. `W`
/// replaces real `core`'s `dyn Write`, as in [`Formatter::new`].
// Excluded from coverage: as for `Arguments::as_str`, the `None` arm cannot be
// reached — no constructor produces a placeholder-carrying `Arguments`.
#[cfg_attr(coverage_nightly, coverage(off))]
#[cfg_attr(charon, aeneas::exclude)]
pub fn write<W: Write>(output: &mut W, args: Arguments) -> Result {
    match args.as_str() {
        Option::Some(s) => output.write_str(s),
        Option::None => Result::Ok(()),
    }
}

// -----------------------------------------------------------------------------
// The remaining formatting traits
// -----------------------------------------------------------------------------

// Each of these traits has a single method called `fmt`, like `Display` and
// `Debug`. F* resolves a typeclass method by its field name, so no two classes
// of a module may call theirs `f_fmt` — hence the per-trait name under
// `hax_backend_fstar` (this is also why `Debug::fmt` is `dbg_fmt` there).
macro_rules! fmt_trait {
    ($Trait:ident, $fstar_name:ident) => {
        #[doc = concat!(" See [`std::fmt::", stringify!($Trait), "`]")]
        pub trait $Trait {
            #[doc = concat!(" See [`std::fmt::", stringify!($Trait), "::fmt`]")]
            #[cfg(not(hax_backend_fstar))]
            fn fmt(&self, f: &mut Formatter) -> Result;
            #[cfg(hax_backend_fstar)]
            fn $fstar_name(&self, f: &mut Formatter) -> Result;
        }
    };
}

fmt_trait!(Binary, binary_fmt);
fmt_trait!(Octal, octal_fmt);
fmt_trait!(LowerHex, lower_hex_fmt);
fmt_trait!(UpperHex, upper_hex_fmt);
fmt_trait!(LowerExp, lower_exp_fmt);
fmt_trait!(UpperExp, upper_exp_fmt);
// Real `core` implements `Pointer` for raw pointers and references only, and the
// model has no raw pointers, so this trait is left without instances.
fmt_trait!(Pointer, pointer_fmt);

macro_rules! impl_fmt_trait_for {
    ($Trait:ident, $fstar_name:ident, $t:ty) => {
        impl $Trait for $t {
            #[cfg(not(hax_backend_fstar))]
            fn fmt(&self, f: &mut Formatter) -> Result {
                Result::Ok(())
            }
            #[cfg(hax_backend_fstar)]
            fn $fstar_name(&self, f: &mut Formatter) -> Result {
                Result::Ok(())
            }
        }
    };
}

// Real `core` implements all six for every integer type; stubbed to `Ok(())`
// like the `Display` impls above.
macro_rules! impl_numeric_fmt_traits_for_ints {
    ($($t:ty),*) => {
        $(
            impl_fmt_trait_for!(Binary, binary_fmt, $t);
            impl_fmt_trait_for!(Octal, octal_fmt, $t);
            impl_fmt_trait_for!(LowerHex, lower_hex_fmt, $t);
            impl_fmt_trait_for!(UpperHex, upper_hex_fmt, $t);
            impl_fmt_trait_for!(LowerExp, lower_exp_fmt, $t);
            impl_fmt_trait_for!(UpperExp, upper_exp_fmt, $t);
        )*
    };
}

impl_numeric_fmt_traits_for_ints!(
    core::primitive::u8,
    core::primitive::u16,
    core::primitive::u32,
    core::primitive::u64,
    core::primitive::u128,
    core::primitive::usize,
    core::primitive::i8,
    core::primitive::i16,
    core::primitive::i32,
    core::primitive::i64,
    core::primitive::i128,
    core::primitive::isize
);

// -----------------------------------------------------------------------------
// `Debug` builders and `from_fn`
// -----------------------------------------------------------------------------
//
// The builders are what a hand-written `Debug` impl builds its output with. Since
// the model's `Formatter` renders nothing, they hold no borrow of it and
// accumulate nothing: every builder method is the identity and every `finish`
// succeeds. The one piece of real behaviour is `DebugMap`'s key/value
// interleaving, which panics in real `core` and here too.
//
// Real `core` takes the values as `&dyn Debug`; the model takes a generic
// reference, because `dyn` has no counterpart in the F* proof libraries. The
// chaining methods return `&mut Self` like real `core`, and are therefore dropped
// from the F* extraction — see the note on `FormattingOptions`' setters.
//
// Real `core` defines all of these in a private `core::fmt::builders` module and
// re-exports them. The model deliberately does *not* mirror that nesting (unlike
// `num_buffer` below): since the builders mention `Formatter` and `Formatter`
// mentions them, the resulting module cycle makes hax emit two conflicting copies
// of the whole of `Core_models.Fmt`. The cost is that the extracted names sit
// under `fmt` rather than under `fmt::builders`.

/// See [`std::fmt::DebugStruct`]
pub struct DebugStruct;

impl DebugStruct {
    /// See [`std::fmt::DebugStruct::field`]
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn field<T: Debug>(&mut self, name: &str, value: &T) -> &mut Self {
        self
    }

    /// See [`std::fmt::DebugStruct::field_with`]
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn field_with<F: FnOnce(&mut Formatter) -> Result>(
        &mut self,
        name: &str,
        value_fmt: F,
    ) -> &mut Self {
        self
    }

    /// See [`std::fmt::DebugStruct::finish_non_exhaustive`]
    pub fn finish_non_exhaustive(&mut self) -> Result {
        Result::Ok(())
    }

    /// See [`std::fmt::DebugStruct::finish`]
    pub fn finish(&mut self) -> Result {
        Result::Ok(())
    }
}

/// See [`std::fmt::DebugTuple`]
pub struct DebugTuple;

impl DebugTuple {
    /// See [`std::fmt::DebugTuple::field`]
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn field<T: Debug>(&mut self, value: &T) -> &mut Self {
        self
    }

    /// See [`std::fmt::DebugTuple::field_with`]
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn field_with<F: FnOnce(&mut Formatter) -> Result>(&mut self, value_fmt: F) -> &mut Self {
        self
    }

    /// See [`std::fmt::DebugTuple::finish_non_exhaustive`]
    pub fn finish_non_exhaustive(&mut self) -> Result {
        Result::Ok(())
    }

    /// See [`std::fmt::DebugTuple::finish`]
    pub fn finish(&mut self) -> Result {
        Result::Ok(())
    }
}

/// See [`std::fmt::DebugList`]
pub struct DebugList;

impl DebugList {
    /// See [`std::fmt::DebugList::entry`]
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn entry<T: Debug>(&mut self, entry: &T) -> &mut Self {
        self
    }

    /// See [`std::fmt::DebugList::entry_with`]
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn entry_with<F: FnOnce(&mut Formatter) -> Result>(&mut self, entry_fmt: F) -> &mut Self {
        self
    }

    /// See [`std::fmt::DebugList::entries`]
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn entries<D: Debug, I: crate::iter::traits::collect::IntoIterator<Item = D>>(
        &mut self,
        entries: I,
    ) -> &mut Self {
        self
    }

    /// See [`std::fmt::DebugList::finish_non_exhaustive`]
    pub fn finish_non_exhaustive(&mut self) -> Result {
        Result::Ok(())
    }

    /// See [`std::fmt::DebugList::finish`]
    pub fn finish(&mut self) -> Result {
        Result::Ok(())
    }
}

/// See [`std::fmt::DebugSet`]
pub struct DebugSet;

impl DebugSet {
    /// See [`std::fmt::DebugSet::entry`]
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn entry<T: Debug>(&mut self, entry: &T) -> &mut Self {
        self
    }

    /// See [`std::fmt::DebugSet::entry_with`]
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn entry_with<F: FnOnce(&mut Formatter) -> Result>(&mut self, entry_fmt: F) -> &mut Self {
        self
    }

    /// See [`std::fmt::DebugSet::entries`]
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn entries<D: Debug, I: crate::iter::traits::collect::IntoIterator<Item = D>>(
        &mut self,
        entries: I,
    ) -> &mut Self {
        self
    }

    /// See [`std::fmt::DebugSet::finish_non_exhaustive`]
    pub fn finish_non_exhaustive(&mut self) -> Result {
        Result::Ok(())
    }

    /// See [`std::fmt::DebugSet::finish`]
    pub fn finish(&mut self) -> Result {
        Result::Ok(())
    }
}

/// See [`std::fmt::DebugMap`]
///
/// `has_key` tracks a key waiting for its value, so that the model panics
/// exactly where real `core` asserts.
pub struct DebugMap {
    has_key: bool,
}

#[hax_lib::attributes]
impl DebugMap {
    /// See [`std::fmt::DebugMap::entry`]
    ///
    /// Panics if a previous key is still waiting for its value.
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn entry<K: Debug, V: Debug>(&mut self, key: &K, value: &V) -> &mut Self {
        self.key(key).value(value)
    }

    // `key`/`value` spell the state change out instead of delegating to
    // `key_with`/`value_with` with a `|f| ..` closure the way real `core` does:
    // neither backend can give an `FnOnce` instance to a closure taking
    // `&mut Formatter`, since their `Fn*` traits have no write-back for it.
    //
    // The panic is a statement rather than the tail of a branch for the same kind
    // of reason: as the result of a `-> &mut Self` method, Aeneas gives the
    // diverging call the shape of a value/write-back pair and then fails to
    // destructure it.

    /// See [`std::fmt::DebugMap::key`]
    ///
    /// Panics if a previous key is still waiting for its value.
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn key<K: Debug>(&mut self, key: &K) -> &mut Self {
        if self.has_key {
            // "attempted to begin a new map entry without completing the previous one"
            crate::panicking::internal::panic()
        }
        self.has_key = true;
        self
    }

    /// See [`std::fmt::DebugMap::key_with`]
    ///
    /// Panics if a previous key is still waiting for its value.
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn key_with<F: FnOnce(&mut Formatter) -> Result>(&mut self, key_fmt: F) -> &mut Self {
        if self.has_key {
            // "attempted to begin a new map entry without completing the previous one"
            crate::panicking::internal::panic()
        }
        self.has_key = true;
        self
    }

    /// See [`std::fmt::DebugMap::value`]
    ///
    /// Panics unless a key is waiting for its value.
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn value<V: Debug>(&mut self, value: &V) -> &mut Self {
        if self.has_key == false {
            // "attempted to format a map value before its key"
            crate::panicking::internal::panic()
        }
        self.has_key = false;
        self
    }

    /// See [`std::fmt::DebugMap::value_with`]
    ///
    /// Panics unless a key is waiting for its value.
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn value_with<F: FnOnce(&mut Formatter) -> Result>(&mut self, value_fmt: F) -> &mut Self {
        if self.has_key == false {
            // "attempted to format a map value before its key"
            crate::panicking::internal::panic()
        }
        self.has_key = false;
        self
    }

    /// See [`std::fmt::DebugMap::entries`]
    ///
    /// Panics if a previous key is still waiting for its value.
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    pub fn entries<
        K: Debug,
        V: Debug,
        I: crate::iter::traits::collect::IntoIterator<Item = (K, V)>,
    >(
        &mut self,
        entries: I,
    ) -> &mut Self {
        self
    }

    /// See [`std::fmt::DebugMap::finish_non_exhaustive`]
    #[hax_lib::requires(self.has_key == false)]
    pub fn finish_non_exhaustive(&mut self) -> Result {
        if self.has_key {
            // "attempted to finish a map with a partial entry"
            crate::panicking::internal::panic()
        } else {
            Result::Ok(())
        }
    }

    /// See [`std::fmt::DebugMap::finish`]
    #[hax_lib::requires(self.has_key == false)]
    pub fn finish(&mut self) -> Result {
        if self.has_key {
            // "attempted to finish a map with a partial entry"
            crate::panicking::internal::panic()
        } else {
            Result::Ok(())
        }
    }
}

/// See [`std::fmt::FromFn`]
pub struct FromFn<F>(F);

/// See [`std::fmt::from_fn`]
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
pub fn from_fn<F: Fn(&mut Formatter) -> Result>(f: F) -> FromFn<F> {
    FromFn(f)
}

// Only `Display`: `Debug` is blanket-implemented above, so a `Debug for FromFn`
// impl would overlap with it.
//
// This impl is the one item of the module that has to *call* a closure taking
// `&mut Formatter`, and no backend can express that: neither `ops::function::Fn`
// nor its Lean counterpart carries a write-back for the `&mut` argument, so the
// call's result type does not match the trait's output. Dropped from both
// extractions; `from_fn` and `FromFn` itself stay, and `from_fn` is dropped from
// F* only because its `Fn` bound mentions `&mut Formatter`.
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
#[cfg_attr(charon, aeneas::exclude)]
impl<F: Fn(&mut Formatter) -> Result> Display for FromFn<F> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        (self.0)(f)
    }
}

mod num_buffer {
    /// See [`std::fmt::NumBufferTrait`]
    pub trait NumBufferTrait {
        /// See [`std::fmt::NumBufferTrait::BUF_SIZE`]
        const BUF_SIZE: core::primitive::usize;
    }

    // Real `core` computes these as `MAX.ilog(10) + 1` (`+ 2` for the sign); the
    // model has no `ilog`, so the values are spelled out. `usize`/`isize` are the
    // 64-bit ones, as everywhere else in the model.
    macro_rules! impl_num_buffer_trait {
        ($($t:ty => $size:expr),* $(,)?) => {
            $(
                impl NumBufferTrait for $t {
                    const BUF_SIZE: core::primitive::usize = $size;
                }
            )*
        };
    }

    impl_num_buffer_trait!(
        core::primitive::u8 => 3,
        core::primitive::i8 => 4,
        core::primitive::u16 => 5,
        core::primitive::i16 => 6,
        core::primitive::u32 => 10,
        core::primitive::i32 => 11,
        core::primitive::u64 => 20,
        core::primitive::i64 => 20,
        core::primitive::u128 => 39,
        core::primitive::i128 => 40,
        core::primitive::usize => 20,
        core::primitive::isize => 20,
    );

    /// See [`std::fmt::NumBuffer`]
    ///
    /// Real `core` holds `[MaybeUninit<u8>; 40]`; the model has no `MaybeUninit`, so
    /// the bytes are zeroed instead. The length is the same 40 real `core` uses (it
    /// does not depend on `T::BUF_SIZE`), which is what `capacity` reports.
    pub struct NumBuffer<T: NumBufferTrait> {
        buf: [core::primitive::u8; 40],
        phantom: std::marker::PhantomData<T>,
    }

    impl<T: NumBufferTrait> NumBuffer<T> {
        /// See [`std::fmt::NumBuffer::new`]
        pub fn new() -> Self {
            NumBuffer {
                buf: [0; 40],
                phantom: std::marker::PhantomData,
            }
        }

        /// See [`std::fmt::NumBuffer::capacity`]
        pub fn capacity(&self) -> core::primitive::usize {
            40
        }
    }
}

pub use num_buffer::{NumBuffer, NumBufferTrait};

mod rt {
    // F*-only: `charon::opaque` drops the declaration too, and `Argument`'s
    // field still names this type, so Lean would not elaborate.
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    // The internals of this are not important in this model
    enum ArgumentType<'a> {
        Placeholder {
            /* value: NonNull<()>,
            formatter: unsafe fn(NonNull<()>, &mut Formatter<'_>) -> Result, */
            _lifetime: std::marker::PhantomData<&'a ()>,
        },
        /* Count(u16), */
    }

    pub struct Argument<'a> {
        ty: ArgumentType<'a>,
    }

    // The formatting arguments carry no observable payload in this model, so
    // every constructor below yields the single placeholder value. Opaque like
    // `ArgumentType` itself: charon drops that enum's variants, so a body
    // building one would leave aeneas without the fields.
    #[hax_lib::opaque]
    fn placeholder<'a>() -> ArgumentType<'a> {
        ArgumentType::Placeholder {
            _lifetime: std::marker::PhantomData,
        }
    }

    impl Argument<'_> {
        #[hax_lib::opaque]
        fn new_display<T>(x: &T) -> Self {
            Argument { ty: placeholder() }
        }
        #[hax_lib::opaque]
        fn new_debug<T>(x: &T) -> Self {
            Argument { ty: placeholder() }
        }
        #[hax_lib::opaque]
        fn new_lower_hex<T>(x: &T) -> Self {
            Argument { ty: placeholder() }
        }
    }
    impl<'a> Argument<'a> {
        #[hax_lib::opaque]
        fn new_binary<T>(x: &T) -> Self {
            Argument { ty: placeholder() }
        }
        #[hax_lib::opaque]
        fn new_const<T, U>(x: &T, y: &U) -> super::Arguments<'a> {
            super::Arguments::from_str("")
        }
        #[hax_lib::opaque]
        fn new_v1<T, U, V, W>(x: &T, y: &U, z: &V, t: &W) -> super::Arguments<'a> {
            super::Arguments::from_str("")
        }
        fn none() -> [Self; 0] {
            []
        }
        #[hax_lib::opaque]
        fn new_v1_formatted<T, U, V>(x: &T, y: &U, z: &V) -> super::Arguments<'a> {
            super::Arguments::from_str("")
        }
    }

    #[cfg(test)]
    mod tests {
        use super::{Argument, ArgumentType};

        /// The `rt` constructors are placeholders (core's real ones build
        /// type-erased trait objects), so all a test can check is that each one
        /// returns the placeholder rather than diverging.
        fn is_placeholder(a: &Argument<'_>) -> bool {
            matches!(a.ty, ArgumentType::Placeholder { .. })
        }

        #[test]
        fn test_argument_constructors() {
            assert!(is_placeholder(&Argument::new_display(&1u8)));
            assert!(is_placeholder(&Argument::new_debug(&1u8)));
            assert!(is_placeholder(&Argument::new_lower_hex(&1u8)));
            assert!(is_placeholder(&Argument::new_binary(&1u8)));
            assert!(Argument::none().is_empty());
        }

        #[test]
        fn test_arguments_constructors() {
            // `Arguments` has no observable content either; construction is all
            // there is to check.
            let _ = Argument::new_const(&1u8, &2u8);
            let _ = Argument::new_v1(&1u8, &2u8, &3u8, &4u8);
            let _ = Argument::new_v1_formatted(&1u8, &2u8, &3u8);
        }
    }

    enum Count {
        Is(u16),
        Param(u16),
        Implied,
    }

    struct Placeholder {
        position: usize,
        flags: u32,
        precision: Count,
        width: Count,
    }

    struct UnsafeArg;
}

#[cfg(test)]
mod tests {
    use super::{Arguments, Display, Formatter, FormattingOptions, Result, Write};

    // Everything in this module is a stub returning `Ok(())`: the model has no
    // output buffer, so `Ok(())` is the whole observable behaviour.
    // `fmt::Error` has no `PartialEq`, hence `is_ok` rather than `assert_eq!`.
    #[test]
    fn test_debug_fmt() {
        let mut sink = Sink(String::new());
        let mut f = Formatter::new(&mut sink, FormattingOptions::new());
        #[cfg(not(hax_backend_fstar))]
        assert!(super::Debug::fmt(&1u8, &mut f).is_ok());
        #[cfg(hax_backend_fstar)]
        assert!(super::Debug::dbg_fmt(&1u8, &mut f).is_ok());
    }

    macro_rules! display_tests {
        ($($t:ident),*) => {
            pastey::paste! { $(
                #[test]
                fn [<test_display_ $t>]() {
                    let mut sink = Sink(String::new());
        let mut f = Formatter::new(&mut sink, FormattingOptions::new());
                    assert!(Display::fmt(&(0 as $t), &mut f).is_ok());
                }
            )* }
        };
    }

    display_tests!(
        u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
    );

    #[test]
    fn test_write_fmt() {
        let mut sink = Sink(String::new());
        let mut f = Formatter::new(&mut sink, FormattingOptions::new());
        assert!(Arguments::write_fmt(&mut f, Arguments::from_str("")).is_ok());
    }

    // `Arguments` can only be built inside this module, so `panicking::panic_fmt`
    // is exercised here rather than next to the other `panicking` tests.
    #[test]
    #[should_panic]
    fn test_panic_fmt() {
        crate::panicking::panic_fmt(Arguments::from_str(""));
    }

    use crate::option::Option as MOption;
    use crate::result::Result as MResult;
    use crate::testing::{Inject, panics_like_core};
    use proptest::prelude::*;

    /// A [`super::Write`] sink that keeps what it is handed, so the operations
    /// that really do produce output (`write_char`, `write`) can be compared
    /// against std's on the resulting string.
    struct Sink(String);

    impl super::Write for Sink {
        fn write_str(&mut self, s: &str) -> super::Result {
            self.0.push_str(s);
            super::Result::Ok(())
        }
    }

    /// A `{}` formatter. Its sink is dropped on purpose: the model's `Formatter`
    /// does not borrow it (see the module docs).
    fn formatter() -> super::Formatter {
        let mut sink = Sink(String::new());
        super::FormattingOptions::new().create_formatter(&mut sink)
    }

    // The three option enums, picked by index so that the std side and the model
    // side are given the same value.
    fn std_sign(i: u8) -> Option<std::fmt::Sign> {
        match i {
            0 => Some(std::fmt::Sign::Plus),
            1 => Some(std::fmt::Sign::Minus),
            _ => None,
        }
    }

    fn std_align(i: u8) -> Option<std::fmt::Alignment> {
        match i {
            0 => Some(std::fmt::Alignment::Left),
            1 => Some(std::fmt::Alignment::Right),
            2 => Some(std::fmt::Alignment::Center),
            _ => None,
        }
    }

    fn std_hex(i: u8) -> Option<std::fmt::DebugAsHex> {
        match i {
            0 => Some(std::fmt::DebugAsHex::Lower),
            1 => Some(std::fmt::DebugAsHex::Upper),
            _ => None,
        }
    }

    #[allow(deprecated)]
    fn std_flags(f: &std::fmt::Formatter) -> u32 {
        f.flags()
    }

    proptest! {
        /// Every `FormattingOptions` setter/getter pair round-trips the same way
        /// as std's.
        #[test]
        fn test_formatting_options_getters(
            sign in 0u8..3,
            zero_pad in any::<bool>(),
            alternate in any::<bool>(),
            fill in any::<char>(),
            align in 0u8..4,
            width in any::<Option<u16>>(),
            precision in any::<Option<u16>>(),
            hex in 0u8..3,
        ) {
            let mut s = std::fmt::FormattingOptions::new();
            s.sign(std_sign(sign))
                .sign_aware_zero_pad(zero_pad)
                .alternate(alternate)
                .fill(fill)
                .align(std_align(align))
                .width(width)
                .precision(precision)
                .debug_as_hex(std_hex(hex));

            let mut m = super::FormattingOptions::new();
            m.sign(std_sign(sign).inject())
                .sign_aware_zero_pad(zero_pad)
                .alternate(alternate)
                .fill(fill)
                .align(std_align(align).inject())
                .width(width.inject())
                .precision(precision.inject())
                .debug_as_hex(std_hex(hex).inject());

            prop_assert_eq!(m.get_sign(), s.get_sign().inject());
            prop_assert_eq!(m.get_sign_aware_zero_pad(), s.get_sign_aware_zero_pad());
            prop_assert_eq!(m.get_alternate(), s.get_alternate());
            prop_assert_eq!(m.get_fill(), s.get_fill());
            prop_assert_eq!(m.get_align(), s.get_align().inject());
            prop_assert_eq!(m.get_width(), s.get_width().inject());
            prop_assert_eq!(m.get_precision(), s.get_precision().inject());
            prop_assert_eq!(m.get_debug_as_hex(), s.get_debug_as_hex().inject());
        }

        /// A `Formatter` built from those options answers the queries the same
        /// way std's does.
        #[test]
        fn test_formatter_getters(
            sign in 0u8..3,
            zero_pad in any::<bool>(),
            alternate in any::<bool>(),
            fill in any::<char>(),
            align in 0u8..4,
            width in any::<Option<u16>>(),
            precision in any::<Option<u16>>(),
            hex in 0u8..3,
        ) {
            let mut s = std::fmt::FormattingOptions::new();
            s.sign(std_sign(sign))
                .sign_aware_zero_pad(zero_pad)
                .alternate(alternate)
                .fill(fill)
                .align(std_align(align))
                .width(width)
                .precision(precision)
                .debug_as_hex(std_hex(hex));
            let mut ssink = String::new();
            let sf = s.create_formatter(&mut ssink);

            let mut m = super::FormattingOptions::new();
            m.sign(std_sign(sign).inject())
                .sign_aware_zero_pad(zero_pad)
                .alternate(alternate)
                .fill(fill)
                .align(std_align(align).inject())
                .width(width.inject())
                .precision(precision.inject())
                .debug_as_hex(std_hex(hex).inject());
            let mut msink = Sink(String::new());
            let mf = m.create_formatter(&mut msink);

            prop_assert_eq!(mf.width(), sf.width().inject());
            prop_assert_eq!(mf.precision(), sf.precision().inject());
            prop_assert_eq!(mf.fill(), sf.fill());
            prop_assert_eq!(mf.align(), sf.align().inject());
            prop_assert_eq!(mf.sign_plus(), sf.sign_plus());
            prop_assert_eq!(mf.sign_minus(), sf.sign_minus());
            prop_assert_eq!(mf.alternate(), sf.alternate());
            prop_assert_eq!(mf.sign_aware_zero_pad(), sf.sign_aware_zero_pad());
            prop_assert_eq!(mf.sign(), sf.sign().inject());
            prop_assert_eq!(mf.flags(), std_flags(&sf));
            prop_assert_eq!(mf.options().get_width(), sf.options().get_width().inject());
            prop_assert_eq!(mf.options().get_fill(), sf.options().get_fill());
        }

        /// `Formatter::new` reads back the options it was given, and
        /// `with_options` replaces them — a plain `{}` set clears the width.
        #[test]
        fn test_formatter_new_and_with_options(width in any::<Option<u16>>()) {
            let mut so = std::fmt::FormattingOptions::new();
            so.width(width);
            let mut ssink = String::new();
            let mut sf = std::fmt::Formatter::new(&mut ssink, so);

            let mut mo = super::FormattingOptions::new();
            mo.width(width.inject());
            let mut msink = Sink(String::new());
            let mut mf = super::Formatter::new(&mut msink, mo);

            prop_assert_eq!(mf.width(), sf.width().inject());

            let sf = sf.with_options(std::fmt::FormattingOptions::new());
            let mf = mf.with_options(super::FormattingOptions::new());
            prop_assert_eq!(mf.width(), sf.width().inject());
        }

        /// `write_char` is one of the few operations the model really performs:
        /// the sink ends up with the same bytes as std's.
        #[test]
        fn test_write_char(c in any::<char>()) {
            let mut m = Sink(String::new());
            prop_assert_eq!(super::WriteDefaults::write_char(&mut m, c), MResult::Ok(()));

            let mut s = String::new();
            std::fmt::Write::write_char(&mut s, c).unwrap();
            prop_assert_eq!(m.0, s);
        }

        /// So is `write_str`.
        #[test]
        fn test_write_str(s in ".*") {
            let mut m = Sink(String::new());
            prop_assert_eq!(super::Write::write_str(&mut m, &s), MResult::Ok(()));
            prop_assert_eq!(m.0, s);
        }
    }

    /// `write` / `write_fmt` forward a placeholder-free `Arguments` verbatim,
    /// like std.
    #[test]
    fn test_write_literal_arguments() {
        let mut m = Sink(String::new());
        assert_eq!(
            super::write(&mut m, super::Arguments::from_str("hello")),
            MResult::Ok(())
        );
        assert_eq!(
            super::WriteDefaults::write_fmt(&mut m, super::Arguments::from_str(" world")),
            MResult::Ok(())
        );

        let mut s = String::new();
        std::fmt::write(&mut s, format_args!("hello")).unwrap();
        std::fmt::Write::write_fmt(&mut s, format_args!(" world")).unwrap();
        assert_eq!(m.0, s);
    }

    #[test]
    fn test_arguments_as_str() {
        assert_eq!(
            super::Arguments::from_str("hi").as_str(),
            MOption::Some("hi")
        );
        assert_eq!(format_args!("hi").as_str(), Some("hi"));
    }

    /// The operations that would render text: they all succeed and produce
    /// nothing, which is the whole point of the module's `Formatter` (std would
    /// have accumulated `"abc"`, `"abc"`, `"0xff"` and `"abc"` here).
    #[test]
    fn test_formatter_output_is_discarded() {
        let mut f = formatter();
        assert_eq!(f.write_str("abc"), MResult::Ok(()));
        assert_eq!(f.pad("abc"), MResult::Ok(()));
        assert_eq!(f.pad_integral(true, "0x", "ff"), MResult::Ok(()));
        assert_eq!(
            f.write_fmt(super::Arguments::from_str("abc")),
            MResult::Ok(())
        );
        assert_eq!(super::Display::fmt(&1u8, &mut f), MResult::Ok(()));
        // Through the trait: `f.write_str` above resolves to the inherent method
        // of the same name, so `impl Write for Formatter` needs naming.
        assert_eq!(super::Write::write_str(&mut f, "abc"), MResult::Ok(()));
    }

    /// All six numeric formatting traits are implemented for every integer type.
    /// Only in the default configuration: `hax_backend_fstar` renames their
    /// methods (see the trait definitions), the behaviour is the same.
    #[cfg(not(hax_backend_fstar))]
    #[test]
    fn test_numeric_fmt_traits_cover_the_integers() {
        fn check<
            T: super::Binary
                + super::Octal
                + super::LowerHex
                + super::UpperHex
                + super::LowerExp
                + super::UpperExp,
        >(
            x: T,
        ) {
            let mut f = formatter();
            assert_eq!(super::Binary::fmt(&x, &mut f), MResult::Ok(()));
            assert_eq!(super::Octal::fmt(&x, &mut f), MResult::Ok(()));
            assert_eq!(super::LowerHex::fmt(&x, &mut f), MResult::Ok(()));
            assert_eq!(super::UpperHex::fmt(&x, &mut f), MResult::Ok(()));
            assert_eq!(super::LowerExp::fmt(&x, &mut f), MResult::Ok(()));
            assert_eq!(super::UpperExp::fmt(&x, &mut f), MResult::Ok(()));
        }
        check(1u8);
        check(1u16);
        check(1u32);
        check(1u64);
        check(1u128);
        check(1usize);
        check(-1i8);
        check(-1i16);
        check(-1i32);
        check(-1i64);
        check(-1i128);
        check(-1isize);
    }

    /// The same six impls under the F* cfg, where each method carries its own
    /// name rather than `fmt`.
    #[cfg(hax_backend_fstar)]
    #[test]
    fn test_numeric_fmt_traits_cover_the_integers() {
        fn check<
            T: super::Binary
                + super::Octal
                + super::LowerHex
                + super::UpperHex
                + super::LowerExp
                + super::UpperExp,
        >(
            x: T,
        ) {
            let mut f = formatter();
            assert_eq!(super::Binary::binary_fmt(&x, &mut f), MResult::Ok(()));
            assert_eq!(super::Octal::octal_fmt(&x, &mut f), MResult::Ok(()));
            assert_eq!(super::LowerHex::lower_hex_fmt(&x, &mut f), MResult::Ok(()));
            assert_eq!(super::UpperHex::upper_hex_fmt(&x, &mut f), MResult::Ok(()));
            assert_eq!(super::LowerExp::lower_exp_fmt(&x, &mut f), MResult::Ok(()));
            assert_eq!(super::UpperExp::upper_exp_fmt(&x, &mut f), MResult::Ok(()));
        }
        check(1u8);
        check(1u16);
        check(1u32);
        check(1u64);
        check(1u128);
        check(1usize);
        check(-1i8);
        check(-1i16);
        check(-1i32);
        check(-1i64);
        check(-1i128);
        check(-1isize);
    }

    #[test]
    fn test_debug_builders_succeed() {
        let mut f = formatter();
        assert_eq!(
            f.debug_struct("S").field("a", &1u8).finish(),
            MResult::Ok(())
        );
        assert_eq!(
            f.debug_struct("S")
                .field_with("a", write_nothing)
                .finish_non_exhaustive(),
            MResult::Ok(())
        );
        assert_eq!(f.debug_tuple("T").field(&1u8).finish(), MResult::Ok(()));
        assert_eq!(
            f.debug_tuple("T")
                .field_with(write_nothing)
                .finish_non_exhaustive(),
            MResult::Ok(())
        );
        assert_eq!(
            f.debug_list()
                .entry(&1u8)
                .entry_with(write_nothing)
                .entries([2u8, 3u8])
                .finish(),
            MResult::Ok(())
        );
        assert_eq!(f.debug_list().finish_non_exhaustive(), MResult::Ok(()));
        assert_eq!(
            f.debug_set()
                .entry(&1u8)
                .entry_with(write_nothing)
                .entries([2u8, 3u8])
                .finish(),
            MResult::Ok(())
        );
        assert_eq!(f.debug_set().finish_non_exhaustive(), MResult::Ok(()));
        assert_eq!(
            f.debug_map()
                .entry(&1u8, &2u8)
                .key(&3u8)
                .value(&4u8)
                .key_with(write_nothing)
                .value_with(write_nothing)
                .entries([(5u8, 6u8)])
                .finish(),
            MResult::Ok(())
        );
        assert_eq!(f.debug_map().finish_non_exhaustive(), MResult::Ok(()));
    }

    // Real `core` asserts on a `DebugMap` whose keys and values do not
    // interleave; the model panics in the same three places.
    struct TwoKeys;
    impl std::fmt::Debug for TwoKeys {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            f.debug_map().key(&1u8).key(&2u8).finish()
        }
    }

    struct ValueBeforeKey;
    impl std::fmt::Debug for ValueBeforeKey {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            f.debug_map().value(&1u8).finish()
        }
    }

    struct DanglingKey;
    impl std::fmt::Debug for DanglingKey {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            f.debug_map().key(&1u8).finish()
        }
    }

    #[test]
    fn test_debug_map_second_key_panics() {
        panics_like_core(
            || {
                let mut f = formatter();
                f.debug_map().key(&1u8).key(&2u8).finish()
            },
            || format!("{:?}", TwoKeys),
        );
    }

    #[test]
    fn test_debug_map_value_before_key_panics() {
        panics_like_core(
            || {
                let mut f = formatter();
                f.debug_map().value(&1u8).finish()
            },
            || format!("{:?}", ValueBeforeKey),
        );
    }

    #[test]
    fn test_debug_map_dangling_key_panics() {
        panics_like_core(
            || {
                let mut f = formatter();
                f.debug_map().key(&1u8).finish()
            },
            || format!("{:?}", DanglingKey),
        );
    }

    // The same three misuses through the `*_with` entry points and
    // `finish_non_exhaustive`, which assert in real `core` too.
    // One named function rather than a closure per call site: the model's
    // `key_with`/`value_with` never invoke theirs (there is nowhere to write),
    // so a fresh closure at each call site would be dead code. `from_fn` below
    // is what runs this one.
    fn write_nothing(_: &mut super::Formatter) -> super::Result {
        MResult::Ok(())
    }

    fn write_nothing_std(_: &mut std::fmt::Formatter) -> std::fmt::Result {
        Ok(())
    }

    struct TwoKeysWith;
    impl std::fmt::Debug for TwoKeysWith {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            f.debug_map()
                .key_with(write_nothing_std)
                .key_with(write_nothing_std)
                .finish()
        }
    }

    struct ValueWithBeforeKey;
    impl std::fmt::Debug for ValueWithBeforeKey {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            f.debug_map().value_with(write_nothing_std).finish()
        }
    }

    struct DanglingKeyNonExhaustive;
    impl std::fmt::Debug for DanglingKeyNonExhaustive {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            f.debug_map().key(&1u8).finish_non_exhaustive()
        }
    }

    #[test]
    fn test_debug_map_second_key_with_panics() {
        panics_like_core(
            || {
                let mut f = formatter();
                f.debug_map()
                    .key_with(write_nothing)
                    .key_with(write_nothing)
                    .finish()
            },
            || format!("{:?}", TwoKeysWith),
        );
    }

    #[test]
    fn test_debug_map_value_with_before_key_panics() {
        panics_like_core(
            || {
                let mut f = formatter();
                f.debug_map().value_with(write_nothing).finish()
            },
            || format!("{:?}", ValueWithBeforeKey),
        );
    }

    #[test]
    fn test_debug_map_dangling_key_finish_non_exhaustive_panics() {
        panics_like_core(
            || {
                let mut f = formatter();
                f.debug_map().key(&1u8).finish_non_exhaustive()
            },
            || format!("{:?}", DanglingKeyNonExhaustive),
        );
    }

    /// `from_fn`'s `Display` calls the closure exactly once, like std's — the
    /// model just has nowhere to put what the closure writes.
    // Also the one place a `&mut Formatter` closure is actually invoked, which
    // is what covers `write_nothing`.
    #[test]
    fn test_from_fn_runs_a_named_writer() {
        let value = super::from_fn(write_nothing);
        let mut f = formatter();
        assert_eq!(super::Display::fmt(&value, &mut f), MResult::Ok(()));
    }

    #[test]
    fn test_from_fn_calls_its_closure() {
        let calls = std::cell::Cell::new(0u32);
        let value = super::from_fn(|f: &mut super::Formatter| {
            calls.set(calls.get() + 1);
            f.write_str("x")
        });
        let mut f = formatter();
        assert_eq!(super::Display::fmt(&value, &mut f), MResult::Ok(()));
        assert_eq!(calls.get(), 1);

        let std_calls = std::cell::Cell::new(0u32);
        let rendered = format!(
            "{}",
            std::fmt::from_fn(|f| {
                std_calls.set(std_calls.get() + 1);
                std::fmt::Write::write_str(f, "x")
            })
        );
        assert_eq!(std_calls.get(), 1);
        assert_eq!(rendered, "x");
    }

    #[test]
    fn test_num_buffer_sizes() {
        macro_rules! check {
            ($($t:ty),*) => {$(
                assert_eq!(
                    <$t as super::NumBufferTrait>::BUF_SIZE,
                    <$t as core::fmt::NumBufferTrait>::BUF_SIZE,
                    concat!("BUF_SIZE for ", stringify!($t))
                );
                assert_eq!(
                    super::NumBuffer::<$t>::new().capacity(),
                    core::fmt::NumBuffer::<$t>::new().capacity()
                );
            )*};
        }
        check!(
            u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize
        );
    }
}
