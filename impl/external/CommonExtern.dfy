module Impl.CommonExtern {
  method {:extern "bv_common", "c_assert"} {:axiom} RuntimeAssert(condition: bool)
    ensures condition
}