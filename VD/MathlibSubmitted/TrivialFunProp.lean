import VD.MathlibSubmitted.MeanValue
import VD.MathlibSubmitted.TrivialIntervalCongruence


@[fun_prop] theorem ContinuousWithinAt.smul'
    {M : Type u_1} {X : Type u_2} {Y : Type u_3}
    [TopologicalSpace M] [TopologicalSpace X] [TopologicalSpace Y]
    [SMul M X] [ContinuousSMul M X] {f : Y → M} {g : Y → X} {b : Y} {s : Set Y}
    (hf : ContinuousWithinAt f s b) (hg : ContinuousWithinAt g s b) :
    ContinuousWithinAt (fun x => f x • g x) s b :=
  Filter.Tendsto.smul hf hg
