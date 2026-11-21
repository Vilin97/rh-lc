import Mathlib
import Formalism.LocalToGlobal.Columns.WordFin
import Formalism.LocalToGlobal.Columns.ReferenceKernelEquivOfLastComponent
import Formalism.LocalToGlobal.Columns.ChainInst
import Formalism.LocalToGlobal.Columns.RecLevelSym
import Formalism.LocalToGlobal.KernelLattices.ColInst
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.Columns.ChainInstY

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Sel

variable {X : Fields} (Pr : Primes X)

theorem exists_over (X : Fields) (v : HeightOneSpectrum (𝓞 X.F)) :
    ∃ P : HeightOneSpectrum (𝓞 X.E), P.asIdeal.under (𝓞 X.F) = v.asIdeal := by
  have hinj : Function.Injective (algebraMap (𝓞 X.F) (𝓞 X.E)) := FaithfulSMul.algebraMap_injective (𝓞 X.F) (𝓞 X.E)
  have hv := v.isPrime
  obtain ⟨Q, _, hQ, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 X.E))
    (by rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]; exact bot_le)
  refine ⟨⟨Q, hQ, ?_⟩, hc⟩
  rintro rfl
  exact v.ne_bot (hc ▸ Ideal.comap_bot_of_injective _ hinj)

open Classical in

end Sel

section Fin

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (Gc : ChGlob X R.m)

abbrev chr0 (X : Fields) (S : Set ℕ) : Chr X.F X.E X.K := ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)

open Classical in

variable (R) in

end Fin

section Dat

variable (d : ColDat) (S : Set ℕ)

end Dat

end Formalism.L2.Ker
