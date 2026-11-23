module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiSTmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcretePeriodDeRhamModuleFinrankLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExtFixing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeBasisOfAdaptedInvariantFamilyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdemNotMemFilVOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiSTmul
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardEqOfLinIndepSpanningDeRham

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

namespace GlobalTheory

theorem card_eq_of_indep_spans_dR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (a m : ℕ) (w : Fin m → Fin a → P.R.BdR), (∀ β : Fin m → P.R.BdR, ∑ i, β i • w i = 0 → β = 0) → (∀ j, ∃ u : Fin m → P.R.BdR, ∑ i, u i • w i = Pi.single j 1) → m = a := by
  intro l _ P AI T a m w hind hspan
  haveI : Nontrivial P.R.BdR := (GlobalTheory.DRFil.isField_dR T).nontrivial
  have hli : LinearIndependent P.R.BdR w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    exact congrFun (hind g hg) i
  have h1 : m ≤ a := by
    have := hli.fintype_card_le_finrank
    simpa [Module.finrank_fin_fun] using this
  have hsurj : Function.Surjective (Fintype.linearCombination P.R.BdR w) := by
    rw [← LinearMap.range_eq_top, Submodule.eq_top_iff']
    intro x
    have hj : ∀ j, Pi.single j (x j) ∈ LinearMap.range (Fintype.linearCombination P.R.BdR w) := by
      intro j
      obtain ⟨u, hu⟩ := hspan j
      refine ⟨x j • u, ?_⟩
      rw [map_smul, Fintype.linearCombination_apply, hu]
      ext k
      by_cases h : k = j
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [← Finset.univ_sum_single x]
    exact Submodule.sum_mem _ fun j _ => hj j
  have h2 : a ≤ m := by
    simpa using card_le_of_surjective P.R.BdR _ hsurj
  exact le_antisymm h1 h2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardEqOfLinIndepSpanningDeRhamStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt


theorem _root_.GlobalTheory.T.card_eq_of_linIndep_spanning_deRham : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (a m : ℕ) (w : Fin m → Fin a → P.R.BdR), (∀ β : Fin m → P.R.BdR, ∑ i, β i • w i = 0 → β = 0) → (∀ j, ∃ u : Fin m → P.R.BdR, ∑ i, u i • w i = Pi.single j 1) → m = a := by
  first | exact @GlobalTheory.card_eq_of_indep_spans_dR | exact GlobalTheory.card_eq_of_indep_spans_dR | (intros; apply GlobalTheory.card_eq_of_indep_spans_dR <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiKernelKillingElement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

noncomputable section
namespace GlobalTheory.HodgeAt

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (σ : GQ l) (L : FinExt l)

theorem phiS_map_emb (u : ↥L.1 ⊗[ℚ_[l]] ↥L.1) :
    phiS P σ L (Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L) u) =
      emb P σ L (Algebra.TensorProduct.lift (AlgHom.id ℚ_[l] ↥L.1) (AlgHom.id ℚ_[l] ↥L.1)
        (fun _ _ => Commute.all _ _) u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul c d => simp [phiS, map_mul]

theorem key_emb (t : ↥L.1 ⊗[ℚ_[l]] ↥L.1)
    (ht : ∀ c : ↥L.1, ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] c) * t = (AlgHom.id ℚ_[l] ↥L.1) c • t) (c : ↥L.1) :
    ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] emb P σ L c) * Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L) t =
      (c ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) * Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L) t := by
  have h := congrArg (Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L)) (ht c)
  rw [map_mul, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] at h
  rw [h, Algebra.smul_def, map_mul]
  congr 1
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  simp

theorem mul_eq_mul_phiS (e : ↥L.1 ⊗[ℚ_[l]] P.R.BdR)
    (hkey : ∀ c : ↥L.1, ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] emb P σ L c) * e = (c ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) * e)
    (s : ↥L.1 ⊗[ℚ_[l]] P.R.BdR) : e * s = e * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] phiS P σ L s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [mul_add, hx, hy, map_add (f := _), TensorProduct.tmul_add, mul_add]
  | tmul c b =>
    calc e * (c ⊗ₜ[ℚ_[l]] b) = ((c ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) * e) * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) := by
          rw [mul_comm (c ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) e, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul]
      _ = (((1 : ↥L.1) ⊗ₜ[ℚ_[l]] emb P σ L c) * e) * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) := by rw [hkey]
      _ = e * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] phiS P σ L (c ⊗ₜ[ℚ_[l]] b)) := by
          rw [mul_comm ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] emb P σ L c) e, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
            one_mul, phiS_tmul, emb_apply]

theorem sm_eq_zero_of_PhiS (a : ℕ) (e : ↥L.1 ⊗[ℚ_[l]] P.R.BdR)
    (hmul : ∀ s : ↥L.1 ⊗[ℚ_[l]] P.R.BdR, e * s = e * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] phiS P σ L s))
    (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) (hx : PhiS P σ L a x = 0) :
    GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) e x = 0 := by
  have hc : ∀ i, phiS P σ L (GlobalTheory.DRFil.ext ℚ_[l] P.R.BdR ((Pi.basisFun ↥L.1 (Fin a)).coord i) x) = 0 := by
    intro i
    have : (Pi.basisFun ↥L.1 (Fin a)).coord i = (LinearMap.proj i : (Fin a → ↥L.1) →ₗ[↥L.1] ↥L.1) := by
      ext v; simp
    rw [this]
    exact congrFun hx i
  have hsum := GlobalTheory.DRFil.eq_sum_basis (Qp := ℚ_[l]) (F := P.R.BdR) (Pi.basisFun ↥L.1 (Fin a)) x

  rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← GlobalTheory.DRFil.sm_mul, hmul, hc i, TensorProduct.tmul_zero, mul_zero]
  simp

end GlobalTheory.HodgeAt

theorem GlobalTheory.HodgeAt.exists_idem_phiS_ker : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (σ : GQ l) (L : FinExt l) [FiniteDimensional ℚ_[l] ↥L.1] (a : ℕ), ∃ e : ↥L.1 ⊗[ℚ_[l]] P.R.BdR, phiS P σ L e = 1 ∧ ∀ x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR, PhiS P σ L a x = 0 → GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) e x = 0 := by
  intro l _ P σ L _ a
  obtain ⟨t, ht1, ht2⟩ := GlobalTheory.DRFil.exists_idem (Qp := ℚ_[l]) (AlgHom.id ℚ_[l] ↥L.1)
  refine ⟨Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L) t, ?_, ?_⟩
  · rw [phiS_map_emb, ht1, map_one]
  · exact sm_eq_zero_of_PhiS P σ L a _ (mul_eq_mul_phiS P σ L _ (key_emb P σ L t ht2))
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiKernelKillingElementStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt


theorem _root_.GlobalTheory.T.exists_bdR_element_normalized_killing_phi_kernel : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (σ : GQ l) (L : FinExt l) [FiniteDimensional ℚ_[l] ↥L.1] (a : ℕ), ∃ e : ↥L.1 ⊗[ℚ_[l]] P.R.BdR, phiS P σ L e = 1 ∧ ∀ x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR, PhiS P σ L a x = 0 → GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) e x = 0 := by
  first | (exact @GlobalTheory.HodgeAt.exists_idem_phiS_ker) | (exact GlobalTheory.HodgeAt.exists_idem_phiS_ker) | (intros; apply GlobalTheory.HodgeAt.exists_idem_phiS_ker  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorDeRhamCoordMulGaloisAction

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

noncomputable section
namespace GlobalTheory.HodgeAt

theorem PhiS_act : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K L : FinExt l) (σ : GQ l) (a : ℕ) (r : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), (∀ g v, R g v = (r g).val *ᵥ v) → ∀ g : ↥(GK K), (∀ y : ↥L.1, (g : GQ l) (σ (y : Om l)) = σ (y : Om l)) → ∀ x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR, PhiS P σ L a (actVdR (P.PD K) R g x) = ((r g).val.map fun y => algebraMap (Om l) P.R.BdR (σ (y : Om l))) *ᵥ fun i => P.actQdR (g : GQ l) (PhiS P σ L a x i) := by
  intro l _ P K L σ a r R hR g hg x
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, PhiS_zero, Pi.zero_apply]
    exact (Matrix.mulVec_zero _).symm
  | add x y hx hy =>
    rw [map_add (f := _), PhiS_add, hx, hy, PhiS_add]
    rw [← Matrix.mulVec_add]
    congr 1
    ext i
    simp only [Pi.add_apply, map_add]
  | tmul v b =>
    rw [GlobalTheory.DRFil.actVdR_tmul, P.PD_actdR, hR, PhiS_tmul, PhiS_tmul]
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]

    simp only [IntermediateField.coe_sum, IntermediateField.coe_mul, map_sum, map_mul, Finset.sum_mul,
    P.actQdR_Om, hg, mul_assoc]

end GlobalTheory.HodgeAt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorDeRhamCoordMulGaloisActionStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt


theorem _root_.GlobalTheory.T.tensorDeRhamCoordMul_galois_action : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K L : FinExt l) (σ : GQ l) (a : ℕ) (r : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), (∀ g v, R g v = (r g).val *ᵥ v) → ∀ g : ↥(GK K), (∀ y : ↥L.1, (g : GQ l) (σ (y : Om l)) = σ (y : Om l)) → ∀ x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR, PhiS P σ L a (actVdR (P.PD K) R g x) = ((r g).val.map fun y => algebraMap (Om l) P.R.BdR (σ (y : Om l))) *ᵥ fun i => P.actQdR (g : GQ l) (PhiS P σ L a x i) := by
  first | exact @GlobalTheory.HodgeAt.PhiS_act | exact GlobalTheory.HodgeAt.PhiS_act | (intros; apply GlobalTheory.HodgeAt.PhiS_act <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeBasisAtEmbedding

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.HodgeAt



theorem exists_hodge_at_embedding : ∀ (l : ℕ) [Fact l.Prime] (K L : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (a : ℕ) (r : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), (∀ g v, R g v = (r g).val *ᵥ v) → Formalism.MainNotions.N.IsDR (P.PD K) R → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (σ : GQ l), (∀ x : ↥K.1, σ ((τ x : ↥L.1) : Om l) = (x : Om l)) → ∃ (K' : FinExt l) (H : Hodge C ξ (fun g => (r g).val.map fun x => σ (x : Om l)) K'), K.1 ≤ K'.1 ∧ ∀ n : ℤ, ((Finset.univ.filter fun i => (H.p i : ℤ) - H.q = n).card : ℤ) = multV (P.PD K) R τ n := by
  intro l _ K L P AI T C hC ξ hξ a r R hR hDR τ σ hσ
  haveI := K.2
  haveI := L.2
  haveI := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K L (Fin a → ↥L.1) R).1
  obtain ⟨m, d, k, hA⟩ := GlobalTheory.DRFil.exists_adapted (P.PD K) (GlobalTheory.DRFil.isField_dR T) R
    (GlobalTheory.DRFil.filSpans T K L R hDR) τ
  obtain ⟨K', hKK', hK'⟩ := exists_ext_fixing l K L σ
  obtain ⟨e, he1, he0⟩ := GlobalTheory.T.exists_bdR_element_normalized_killing_phi_kernel l P σ L a
  have hid := phiS_idem l P K L τ σ hσ
  set w : Fin m → Fin a → P.R.BdR := fun i => PhiS P σ L a (d i) with hw
  have hfil : ∀ i j, w i j ∈ (P.PD K).Fil (k i) := fun i j =>
    phiS_mem_Fil l P AI T K L σ (k i) _ (GlobalTheory.DRFil.ext_mem_FilV (P.PD K) _ (hA.mem i).2)
  have hind : ∀ β : Fin m → P.R.BdR, ∑ i, β i • w i = 0 → β = 0 := by
    intro β hβ
    have h0 : ∑ i, GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) (e * ((1 : ↥L.1) ⊗ₜ β i)) (d i) = 0 := by

      simp only [GlobalTheory.DRFil.sm_mul, GlobalTheory.DRFil.sm_one_tmul, ← map_sum]
      apply he0
      rw [PhiS_sum]
      simp only [PhiS_mulR]
      rw [← hβ]
      funext j
      simp [hw]
    funext i
    have := congrArg (phiS P σ L) (hA.indep _ h0 i)
    simpa [map_mul, hid, he1, phiS_tmul] using this
  have hspan : ∀ j, ∃ u : Fin m → P.R.BdR, (∀ i, u i ∈ (P.PD K).Fil (-k i)) ∧ ∑ i, u i • w i = Pi.single j 1 := by
    intro j
    obtain ⟨rr, hrr, hy⟩ := hA.span 0 (Pi.single j 1 ⊗ₜ (1 : P.R.BdR))
      (GlobalTheory.DRFil.tmul_mem_FilV (P.PD K) _ (P.PD K).one_mem)
    refine ⟨fun i => phiS P σ L (rr i), fun i => by simpa using phiS_mem_Fil l P AI T K L σ _ _ (hrr i), ?_⟩
    have h2 := congrArg (PhiS P σ L a) hy
    rw [PhiS_sm] at h2
    simp only [hid, one_mul, PhiS_sum, PhiS_sm] at h2
    have h3 : ∑ i, (fun i => phiS P σ L (rr i)) i • w i = ∑ x, fun i => phiS P σ L (rr x) * PhiS P σ L a (d x) i := rfl
    rw [h3, ← h2, PhiS_tmul]
    funext i
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Pi.single_eq_of_ne hij]
  have hinv : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → ∀ i,
      ((fun g => (r g).val.map fun x => σ (x : Om l)) g).map (algebraMap (Om l) P.R.BdR) *ᵥ
        (fun j => P.actQdR (g : GQ l) (w i j)) = w i := by
    intro g hg i
    have h1 := GlobalTheory.T.tensorDeRhamCoordMul_galois_action l P K L σ a r R hR g (fun y => hK' g hg y) (d i)
    rw [(GlobalTheory.DRFil.mem_DdR (P.PD K) R _).1 (hA.mem i).1.1 g] at h1
    rw [Matrix.map_map]
    exact h1.symm
  have hma := GlobalTheory.T.card_eq_of_linIndep_spanning_deRham l P AI T a m w hind (fun j => (hspan j).imp fun u hu => hu.2)
  subst hma
  obtain ⟨H, hH⟩ := GlobalTheory.T.hodge_basis_of_adapted_invariant_family l P AI T C hC ξ hξ K K' m _ w k hfil hspan hinv
  exact ⟨K', H, hKK', fun n => by rw [hH n, hA.multV_eq]⟩

end GlobalTheory.HodgeAt
end
end
