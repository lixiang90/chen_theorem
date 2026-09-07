import ChallengeDeps
import Submission.ChenTheorem.Main

namespace Submission

theorem chen_theorem :
    {p : ℕ | p.Prime ∧ LeanEval.NumberTheory.ChenTheorem.HasAtMostTwoPrimeFactors (p + 2)}.Infinite := by
  apply (Chen.chen_twin 2 (by decide) (by norm_num)).mono
  intro p hp
  refine ⟨hp.1, ?_⟩
  rcases hp.2 with hprime | ⟨a, b, ha, hb, hab⟩
  · exact Or.inl ⟨p + 2, hprime, rfl⟩
  · exact Or.inr ⟨a, b, ha, hb, hab⟩

end Submission
