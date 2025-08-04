import OperatorKernelO6.Kernel
import OperatorKernelO6.Meta.Termination  -- adjust if your SN file lives elsewhere

open Classical
open OperatorKernelO6 Trace Step

namespace OperatorKernelO6.Meta

noncomputable def normalize : Trace → Trace
| t =>
  if h : ∃ u, Step t u then
    let u := Classical.choose h
    have hu : Step t u := Classical.choose_spec h
    normalize u
  else t
termination_by
  normalize t => size t
decreasing_by
  simp_wf
  exact step_size_decrease (Classical.choose_spec h)

theorem to_norm : ∀ t, StepStar t (normalize t)
| t =>
  by
    classical
    by_cases h : ∃ u, Step t u
    ·
      let u := Classical.choose h
      have hu : Step t u := Classical.choose_spec h
      have ih := to_norm u
      simpa [normalize, h, u, hu] using StepStar.tail hu ih
    ·
      simpa [normalize, h] using StepStar.refl t
termination_by
  to_norm t => size t
decreasing_by
  simp_wf
  exact step_size_decrease (Classical.choose_spec h)

theorem norm_nf : ∀ t, NormalForm (normalize t)
| t =>
  by
    classical
    by_cases h : ∃ u, Step t u
    ·
      let u := Classical.choose h
      have hu : Step t u := Classical.choose_spec h
      have ih := norm_nf u
      simpa [normalize, h, u, hu] using ih
    ·
      intro ex
      rcases ex with ⟨u, hu⟩
      have : Step t u := by simpa [normalize, h] using hu
      exact h ⟨u, this⟩
termination_by
  norm_nf t => size t
decreasing_by
  simp_wf
  exact step_size_decrease (Classical.choose_spec h)

theorem nfp {a b n : Trace} (hab : StepStar a b) (han : StepStar a n) (hn : NormalForm n) :
  StepStar b n := by
  revert b
  induction han with
  | refl =>
      intro b hab _; exact hab
  | tail h an han ih =>
      intro b hab hn'
      cases hab with
      | refl => exact False.elim (hn' ⟨_, h⟩)
      | tail h' hbn => exact ih hbn hn'

def Confluent : Prop :=
  ∀ {a b c}, StepStar a b → StepStar a c → ∃ d, StepStar b d ∧ StepStar c d

theorem global_confluence : Confluent := by
  intro a b c hab hac
  let n := normalize a
  have han : StepStar a n := to_norm a
  have hbn : StepStar b n := nfp hab han (norm_nf a)
  have hcn : StepStar c n := nfp hac han (norm_nf a)
  exact ⟨n, hbn, hcn⟩

end OperatorKernelO6.Meta
