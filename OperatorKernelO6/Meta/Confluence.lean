import OperatorKernelO6.Kernel
import Init.WF
import OperatorKernelO6.Meta.Normalize

open OperatorKernelO6 Trace Step
namespace OperatorKernelO6.Meta

def Confluent : Prop :=
  ∀ {a b c}, StepStar a b → StepStar a c → ∃ d, StepStar b d ∧ StepStar c d

theorem global_confluence : Confluent :=
  confluent_via_normalize

end OperatorKernelO6.Meta
