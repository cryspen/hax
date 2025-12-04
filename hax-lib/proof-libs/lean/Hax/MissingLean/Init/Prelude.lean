
@[grind]
theorem System.Platform.two_pow_numBits_eq :
  2 ^ System.Platform.numBits = 4294967296 ∨ 2 ^ System.Platform.numBits = 18446744073709551616 := by
  rcases System.Platform.numBits_eq <;> simp [*]
