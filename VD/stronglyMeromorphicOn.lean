import Mathlib.Analysis.Meromorphic.NormalFormAt
import Mathlib.Analysis.Meromorphic.Divisor
import VD.Divisor_MeromorphicOn
import VD.ToMathlib.NormalForm

open Topology


variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E}
  {x : 𝕜}
  {U : Set 𝕜}


/--
Conversion to normal form on `U` does not affect the divisor.
-/
theorem divisor_toMeromorphicNFOn [CompleteSpace E] (hf : MeromorphicOn f U) :
    MeromorphicOn.divisor f U = MeromorphicOn.divisor (toMeromorphicNFOn f U) U := by
  rw [← hf.divisor_congr_codiscreteWithin (toMeromorphicNFOn_eqOn_codiscrete hf)]
  exact toMeromorphicNFOn_eq_self_on_compl hf
