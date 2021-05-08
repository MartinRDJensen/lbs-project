module Test

module U32 = FStar.UInt32

open U32

let mul (a b: U32.t) = a *%^ b
