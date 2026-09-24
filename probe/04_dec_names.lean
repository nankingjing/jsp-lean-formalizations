-- Probe 04 — which decidable-instance helper names actually exist in core Lean 4?
-- Every line here is a `#check`; failures are reported per-line and the rest still run.
import Init

#check @instDecidableForallNat
#check @instDecidableBallNat
#check @instDecidableBallNatLt
#check @Nat.decidableBallLT
#check @Nat.decidableForallLt
#check @Nat.decidableForallLe
#check @decidableForallNat
#check @decidableBallNatLT
#check List.all
#check List.all_eq_true
#check List.decidableAll
#check List.any
#check @List.decidableBAll
#check Nat.decLt
#check Nat.decLe
#check Nat.find
#check Nat.find_spec
#check Nat.mod_eq_sub_mod
