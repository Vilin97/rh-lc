module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFixesEpsilonRootsResGammaTrivialStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecWOfMatrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleEmbeddingFrobeniusGaloisCompatStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRingImageAddEllPiAdicClosed
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRingImageSaturatedAdicClosedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusConstantsPiAdicFiltrationModEll
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedSubringTensorWittSaturatedComplete
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedTensorWittApproxFrobeniusPerfection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedTensorWittCompletePiAdicModEll
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixFrobeniusSubOneBijectiveModSubring

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecWOfMatrixStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.decW_of_matrix_criterion : ∀ (S : Sit) (E : S.Comparison₂), (∀ (d : ℕ) (Pm : Matrix (Fin d) (Fin d) S.W.EE), (∀ y : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (y i) = y i) → ∃ z : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (z i) = z i) ∧ ∀ i, ∃ e, y i - (∑ k, E.ioE (Pm i k) * S.φR (z k) - z i) = E.ioE e) ∧ (∀ z : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (z i) = z i) → (∀ i, ∃ e, ∑ k, E.ioE (Pm i k) * S.φR (z k) - z i = E.ioE e) → ∀ i, ∃ e, z i = E.ioE e)) → DecW S E := by
  first | exact @GlobalTheory.DecomplRed.decW_of_matrix | exact GlobalTheory.DecomplRed.decW_of_matrix | (intros; apply GlobalTheory.DecomplRed.decW_of_matrix <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRingImageAddEllPiAdicClosedStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.etaleRing_image_add_ell_pi_adic_closed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W) (x : RW LL), (∀ m, ∃ e, NearPi AI LL s m (x - E.tie.ioE e)) → ∃ e r, x - E.tie.ioE e = (l : RW LL) * r := by
  first | exact @GlobalTheory.Decompl.ioE_closed | exact GlobalTheory.Decompl.ioE_closed | (intros; apply GlobalTheory.Decompl.ioE_closed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusConstantsPiAdicFiltrationModEllStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.frobenius_constants_piAdic_filtration_modEll : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (s : ℕ), (∀ a : RA LL, ∃ a' : RA LL, φRW LL (inclR LL a) = inclR LL a') ∧ NearPi AI LL s 2 (φRW LL (piR AI LL s)) ∧ (∀ (m : ℕ) (x : RW LL), NearPi AI LL s m x → NearPi AI LL s m (φRW LL x)) ∧ ∀ o : ↥(OL LL), NearPi AI LL s 1 (algebraMap ↥(OL LL) (RW LL) o) → ∃ o' : ↥(OL LL), o = (l : ↥(OL LL)) * o' := by
  first | exact @GlobalTheory.DecomplFrob.frobenius_and_constants | exact GlobalTheory.DecomplFrob.frobenius_and_constants | (intros; apply GlobalTheory.DecomplFrob.frobenius_and_constants <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedSubringTensorWittSaturatedCompleteStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.galoisFixedSubringTensorWitt_saturated_complete : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (H : Set (GQ l)), (∀ x, (l : RW LL) * x ∈ fixSub AI LL H → x ∈ fixSub AI LL H) ∧ (∀ x ∈ fixSub AI LL H, φRW LL x ∈ fixSub AI LL H) ∧ ∀ x : ℕ → RW LL, (∀ i, x i ∈ fixSub AI LL H) → ∃ y ∈ fixSub AI LL H, ∀ k : ℕ, ∃ r, y - ∑ i ∈ Finset.range k, (l : RW LL) ^ i * x i = (l : RW LL) ^ k * r := by
  first | exact @GlobalTheory.Decompl.FixL.fixSub_ladic | exact GlobalTheory.Decompl.FixL.fixSub_ladic | (intros; apply GlobalTheory.Decompl.FixL.fixSub_ladic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedTensorWittApproxFrobeniusPerfectionStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.galoisFixedTensorWitt_approx_frobeniusPerfection : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), ∀ y ∈ fixSub AI LL (Hinf K : Set (GQ l)), ∀ m : ℕ, ∃ (n : ℕ) (y0 : RW LL) (e : W.EE) (r : RW LL), (φRW LL)^[n] y0 = E.tie.ioE e + (l : RW LL) * r ∧ NearPi AI LL s m (y - y0) := by
  first | exact @GlobalTheory.DecomplDense.fixSub_approx_perfection | exact GlobalTheory.DecomplDense.fixSub_approx_perfection | (intros; apply GlobalTheory.DecomplDense.fixSub_approx_perfection <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedTensorWittCompletePiAdicModEllStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.galoisFixedTensorWitt_complete_piAdic_modEll : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) (H : Set (GQ l)), piR AI LL s ∈ fixSub AI LL H → ∀ (k : ℕ) (f : ℕ → RW LL), (∀ i, f i ∈ fixSub AI LL H) → (∀ i, NearPi AI LL s (i + k) (f i)) → ∃ x ∈ fixSub AI LL H, ∀ m, NearPi AI LL s (m + k) (x - ∑ i ∈ Finset.range m, f i) := by
  first | exact @GlobalTheory.Decompl.fixSub_nearPi_complete | exact GlobalTheory.Decompl.fixSub_nearPi_complete | (intros; apply GlobalTheory.Decompl.fixSub_nearPi_complete <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixFrobeniusSubOneBijectiveModSubringStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.matrix_frobenius_sub_one_bijective_mod_subring : ∀ (R EE A : Type) [CommRing R] [CommRing EE] [CommRing A] (j : EE →+* R) (ι : A →+* R) (φ : R →+* R) (S : Subring R) (p : ℕ) (t : R) (τ : A), ι τ = t → (∀ e, j e ∈ S) → (∀ x ∈ S, φ x ∈ S) → (∀ e, ∃ e', φ (j e) = j e') → (∀ a, ∃ a', φ (ι a) = ι a') → Near ι p t 2 (φ t) → (∀ e, ∃ c : ℕ, Near ι p t 0 (t ^ c * j e)) → (∀ x, (p : R) * x ∈ S → x ∈ S) → (∀ x e, (p : R) * x = j e → ∃ e', x = j e') → (∀ (k : ℕ) (f : ℕ → R), (∀ i, f i ∈ S) → (∀ i, Near ι p t (i + k) (f i)) → ∃ s ∈ S, ∀ m, Near ι p t (m + k) (s - ∑ i ∈ Finset.range m, f i)) → (∀ x, (∀ m, ∃ e, Near ι p t m (x - j e)) → ∃ e r, x - j e = (p : R) * r) → (∀ y ∈ S, ∀ m, ∃ (n : ℕ) (y0 : R) (e : EE) (r : R), φ^[n] y0 = j e + (p : R) * r ∧ Near ι p t m (y - y0)) → (∀ x : ℕ → R, (∀ i, x i ∈ S) → ∃ s ∈ S, ∀ k, ∃ r, s - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * r) → (∀ x, (∀ k : ℕ, ∃ e r, x - j e = (p : R) ^ k * r) → ∃ e, x = j e) → ∀ (d : ℕ) (Pm : Matrix (Fin d) (Fin d) EE), (∀ y : Fin d → R, (∀ i, y i ∈ S) → ∃ z : Fin d → R, (∀ i, z i ∈ S) ∧ ∀ i, ∃ e, y i - (∑ k, j (Pm i k) * φ (z k) - z i) = j e) ∧ (∀ z : Fin d → R, (∀ i, z i ∈ S) → (∀ i, ∃ e, ∑ k, j (Pm i k) * φ (z k) - z i = j e) → ∀ i, ∃ e, z i = j e) := by
  first | exact @GlobalTheory.DecomplMat.matrix_frob_sub_one_bijective | exact GlobalTheory.DecomplMat.matrix_frob_sub_one_bijective | (intros; apply GlobalTheory.DecomplMat.matrix_frob_sub_one_bijective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompletionPhiSubOneBijective

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl



theorem decompletion_matrix (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL)
    (E : EtSit P AI K s LL h W) (H : Set (GQ l))
    (hH : ∀ g, g ∈ H ↔ ∃ hg : g ∈ GK K, W.resΓ ⟨g, hg⟩ = 1)
    (d : ℕ) (Pm : Matrix (Fin d) (Fin d) W.EE) :
    (∀ y : Fin d → RW LL, (∀ i, y i ∈ fixSub AI LL H) → ∃ z : Fin d → RW LL,
      (∀ i, z i ∈ fixSub AI LL H) ∧
        ∀ i, ∃ e, y i - (∑ k, E.tie.ioE (Pm i k) * φRW LL (z k) - z i) = E.tie.ioE e) ∧
    (∀ z : Fin d → RW LL, (∀ i, z i ∈ fixSub AI LL H) →
      (∀ i, ∃ e, ∑ k, E.tie.ioE (Pm i k) * φRW LL (z k) - z i = E.tie.ioE e) →
        ∀ i, ∃ e, z i = E.tie.ioE e) := by
  obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.T.etaleEmbedding_frobenius_galois_compat l P AI K s LL h W E
  obtain ⟨f1, f2, f3⟩ := GlobalTheory.T.galoisFixedSubringTensorWitt_saturated_complete l P AI LL H
  obtain ⟨p1, p2, -, -⟩ := GlobalTheory.T.frobenius_constants_piAdic_filtration_modEll l P AI LL s
  obtain ⟨s1, s2⟩ := GlobalTheory.T.etaleRing_image_saturated_adicClosed l P AI K s LL h W E
  have hE : ∀ e, E.tie.ioE e ∈ fixSub AI LL H := fun e => mem_fixSub.2 fun g hg => by
    obtain ⟨hg, hg1⟩ := (hH g).1 hg
    exact c2 ⟨g, hg⟩ hg1 e
  have hsub : ∀ y ∈ fixSub AI LL H, y ∈ fixSub AI LL (Hinf K : Set (GQ l)) := fun y hy =>
    mem_fixSub.2 fun g hg => mem_fixSub.1 hy g
      ((hH g).2 ((GlobalTheory.T.cyclotomicTower_fixes_epsilonRoots_resGamma_trivial l P AI K).2 s LL h W g hg))
  have hπ : piR AI LL s ∈ fixSub AI LL H := by rw [← c3]; exact hE _
  have q1 := GlobalTheory.T.galoisFixedTensorWitt_complete_piAdic_modEll l P AI LL s H hπ
  have q2 := GlobalTheory.T.etaleRing_image_add_ell_pi_adic_closed l P AI K s LL h W E
  have q3 := fun y hy => GlobalTheory.T.galoisFixedTensorWitt_approx_frobeniusPerfection l P AI K s LL h W E y (hsub y hy)
  have q4 := GlobalTheory.T.matrix_frobenius_sub_one_bijective_mod_subring (RW LL) W.EE (RA LL) (E.tie.ioE : W.EE →+* RW LL) (inclR LL : RA LL →+* RW LL)
    (φRW LL : RW LL →+* RW LL) (fixSub AI LL H) l (piR AI LL s)
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piW AI s) rfl
  simp only [RingHom.coe_coe] at q4
  have q5 := q4 hE f2 (fun e => ⟨W.φE e, (c1 e).symm⟩) p1 p2 c4 f1 s1
  have q6 := q5 q1 q2 q3
  exact q6 f3 s2 d Pm

theorem decompletion : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; DecW S E := by
  intro D HW F l _ K s LL h S E
  refine GlobalTheory.T.decW_of_matrix_criterion S E fun d Pm => ?_
  have hm := decompletion_matrix l (D.loc l) (D.locA l) K s LL h ((HW l).W K s LL h)
    ((F l).E K s LL h) {g | ∃ hg : g ∈ GK K, ((HW l).W K s LL h).resΓ ⟨g, hg⟩ = 1}
    (fun _ => Iff.rfl) d Pm
  have hf : ∀ x : RW LL, x ∈ fixSub (D.locA l) LL
      {g | ∃ hg : g ∈ GK K, ((HW l).W K s LL h).resΓ ⟨g, hg⟩ = 1} ↔
      ∀ g ∈ Hker S, S.gR g x = x := fun x =>
    mem_fixSub.trans ⟨fun hx g hg => hx g.1 ⟨g.2, hg⟩, fun hx g ⟨hg, hg1⟩ => hx ⟨g, hg⟩ hg1⟩
  refine ⟨fun y hy => ?_, fun z hz => hm.2 z fun i => (hf _).2 (hz i)⟩
  obtain ⟨z, hz, hz'⟩ := hm.1 y fun i => (hf _).2 (hy i)
  exact ⟨z, fun i => (hf _).1 (hz i), hz'⟩

end GlobalTheory.Decompl
end
end
