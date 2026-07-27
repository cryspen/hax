-- Hand-written stub. Aeneas emits `FunsExternal_Template.lean` listing
-- axioms for items it can't see the body of (e.g. `core::array::from_fn`,
-- `core::result::Result::*`); those axioms already live in our parent
-- `CoreModels.FunsExternal` module, which is pulled in by `import CoreModels`
-- from the auto-generated `Funs.lean`. So this file just needs to exist
-- (referenced by the auto-generated `import ClientTest.FunsExternal`) and
-- otherwise carry no content of its own.
import Aeneas
