module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCrystalStratificationMatrixStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTaylorShiftFrobeniusTwoVariableCompatible
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RealisesUnitPow
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusStratificationCoeffEqConnectionPowStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConnPhiExtensionGeneratorEqZeta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCrystalCoordinates
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalChangeOfBasisFrobeniusCompatStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallinePrismsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisMatrixEqCrystalChangeOfBasisValueStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatFactorialBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCrystalChangeOfBasisConstantCoeffEqOneStatement
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTaylorFormulaBreuilKisinLattice

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTaylorShiftFrobeniusTwoVariableCompatibleStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_taylorShift_frobenius_twoVariable_compatible : ∀ (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[l] K], ∃ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) ∧ (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) ∧ (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) := by
  first | exact @GlobalTheory.TaylorShift.shift_frob_exists | exact GlobalTheory.TaylorShift.shift_frob_exists | (intros; apply GlobalTheory.TaylorShift.shift_frob_exists <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCrystalBasisAndSpan

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKBasis



theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∃ b : ι → E.M (ϖ.prism a), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) ∧ ∀ x : E.M (ϖ.prism a), ∃ (N : ℕ) (c : ι → Fin N → O) (s : ι → Fin N → (ϖ.prism a).A), x = ∑ j, ∑ q, s j q • (oE (c j q)).u (ϖ.prism a) (b j) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  letI := zlLat T
  intro E jA H him oE hoE
  obtain ⟨J, hJ⟩ : ∃ J : E.M (ϖ.prism a) →+ TW (OW l O) T,
      ∀ x, J x = kappa T (jA (E.tr (ϖ.toAinf a) x)) :=
    ⟨(kappa T).comp (jA.toAddMonoidHom.comp (E.tr (ϖ.toAinf a)).toAddMonoidHom), fun _ => rfl⟩
  have h1 : ∀ y : TW (OW l O) T, (∃ x, y = J x) ↔
      ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) := fun y => by
    simp only [hJ]
    exact him y
  obtain ⟨c, hc, hcJ, hs⟩ := GlobalTheory.BKCoord.exists_coord I J h1
  have hi : Function.Injective J := by
    have := E.proj (ainfObj (ϖ.field a))
    have := E.proj (ϖ.prism a)
    intro x y h
    rw [hJ, hJ] at h
    exact GlobalTheory.BKCoord.semiBC_injective (E.tr_bc (ϖ.toAinf a)) (GlobalTheory.BKCoord.ev_injective ϖ)
      (GlobalTheory.BKCoord.semiBC_injective H.bc inclW_injective ((kappa_bijective T).1 h))
  have hci : Function.Injective c := fun x y hxy => hi (by rw [hcJ, hcJ]; simp only [hxy])
  have hsm : ∀ (w : (ϖ.prism a).A) (x : E.M (ϖ.prism a)),
      c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i := fun w x => by
    refine GlobalTheory.BKCoord.eq_of_j_eq_toAc I w ⟨_, mem_ME_of_mem_M (hc x)⟩ ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_
    have h3 := congrArg jA ((E.tr (ϖ.toAinf a)).map_smulₛₗ w x)
    have h4 := congrArg (kappa T) (h3.trans (jA.map_smulₛₗ _ _))
    have h5 := h4.trans (GlobalTheory.BKCoord.kappa_smul T _ _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h5
  have hom : ∀ (o : O) (x : E.M (ϖ.prism a)),
      c ((oE o).u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i := fun o x => by
    refine GlobalTheory.BKCoord.eq_of_j_eq_const I o ⟨_, mem_ME_of_mem_M (hc x)⟩ ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_
    have h3 := (congrArg jA ((oE o).u_tr (ϖ.toAinf a) x)).symm.trans (hoE o _)
    have hk : ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T,
        kappa T ((OfCrystal.mulZ T o).lTensor (WCb l) y) = o • kappa T y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero, smul_zero]
      | tmul v z => exact tmul_smul o ((1 : O) ⊗ₜ[ℤ_[l]] v : OW l O) z
      | add y y' hy hy' => simp only [map_add (f := _), smul_add, hy, hy']
    have h4 := (congrArg (kappa T) h3).trans (hk _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h4
  have hbas : ∀ j, (bas j : Vec K a ι) ∈ P.M := fun j => mem_tot.2 fun τ i => by
    change (Pi.single j (1 : K⟦X⟧) : ι → K⟦X⟧) i ∈ A O K
    by_cases h : i = j
    · subst h
      rw [Pi.single_eq_same]
      exact one_mem _
    · rw [Pi.single_eq_of_ne h]
      exact zero_mem _
  choose b hb using fun j => hs _ (hbas j)
  refine ⟨b, fun j => ⟨hbas j, ?_⟩, fun x => ?_⟩
  · rw [← hJ, hcJ]
    have e1 : (⟨c (b j), mem_ME_of_mem_M (hc _)⟩ : ME P) = ⟨bas j, mem_ME_of_mem_M (hbas j)⟩ :=
      Subtype.ext (hb j)
    rw [e1]
  · let o := Module.finBasis ℤ_[l] O
    have hf : ∀ i, ∃ s : Fin (Module.finrank ℤ_[l] O) → (Wq l a)⟦X⟧,
        (fun τ => (⟨c x τ i, mem_tot.1 (hc x) τ i⟩ : A O K)) = ∑ q, o q • toAc t K (s q) :=
      fun i => exists_eq_sum_toAc t K o _
    choose s hs' using hf
    refine ⟨Module.finrank ℤ_[l] O, fun _ q => o q, s, hci ?_⟩

    simp only [map_sum, hsm, hom, hb]
    funext τ i
    have h6 := congrArg (fun f : ZMod a → A O K => (f τ : K⟦X⟧)) (hs' i)
    simp only [Finset.sum_apply, Pi.smul_apply, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h6
    rw [h6]
    simp only [Finset.sum_apply]
    symm
    rw [Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun q _ => ?_
      have h7 := hsm (s i q) ((oE (o q)).u (ϖ.prism a) (b i))
      erw [h7, hom, hb]
      simp only [bas, Pi.single_eq_same, mul_one, Algebra.smul_def, algebraMap_eq_C]
      exact mul_comm _ _
    · intro j _ hj
      refine Finset.sum_eq_zero fun q _ => ?_
      have h7 := hsm (s j q) ((oE (o q)).u (ϖ.prism a) (b j))
      erw [h7, hom, hb]
      simp only [bas, Pi.single_eq_of_ne (Ne.symm hj), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
end GlobalTheory.BKBasis
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCrystalBasisAndSpanStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.breuilKisinPrism_crystal_basis_and_span : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∃ b : ι → E.M (ϖ.prism a), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) ∧ ∀ x : E.M (ϖ.prism a), ∃ (N : ℕ) (c : ι → Fin N → O) (s : ι → Fin N → (ϖ.prism a).A), x = ∑ j, ∑ q, s j q • (oE (c j q)).u (ϖ.prism a) (b j) := by
  first | exact @GlobalTheory.BKBasis.main | exact GlobalTheory.BKBasis.main | (intros; apply GlobalTheory.BKBasis.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisDividedTaylorExpansionFrobeniusBasis

section

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysGal

open GlobalTheory.Prism

theorem span_range_tr {l : ℕ} {R : Type} [CommRing R] (E : FCrys l R) {P P' : Obj l R}
    (f : GlobalTheory.Prism.Hom P P') : Submodule.span P'.A (Set.range (E.tr f)) = ⊤ := by
  have hu := (E.tr_bc f (E.M P' ⧸ Submodule.span P'.A (Set.range (E.tr f))) 0).unique
    (y₁ := Submodule.mkQ _) (y₂ := 0)
    (fun x => by
      show Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span ⟨x, rfl⟩)
    (fun x => rfl)
  rw [eq_top_iff]
  intro x _
  have := LinearMap.congr_fun hu x
  rwa [Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero] at this

theorem mem_span_tr {l : ℕ} {R : Type} [CommRing R] (E : FCrys l R) {P P' : Obj l R}
    (f : GlobalTheory.Prism.Hom P P') {O ι : Type} [Fintype ι] (oE : O → FHom E E) (b : ι → E.M P)
    (hgen : ∀ x : E.M P, ∃ (N : ℕ) (c : ι → Fin N → O) (s : ι → Fin N → P.A),
      x = ∑ j, ∑ q, s j q • (oE (c j q)).u P (b j)) (x : E.M P') :
    x ∈ Submodule.span P'.A (Set.range fun p : O × ι => (oE p.1).u P' (E.tr f (b p.2))) := by
  have hx : x ∈ Submodule.span P'.A (Set.range (E.tr f)) := (span_range_tr E f) ▸ Submodule.mem_top
  refine (Submodule.span_le.2 ?_) hx
  rintro _ ⟨z, rfl⟩
  obtain ⟨N, c, s, hz⟩ := hgen z

  rw [hz, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_

  rw [map_sum]
  refine Submodule.sum_mem _ fun q _ => ?_
  rw [map_smulₛₗ, ← (oE (c j q)).u_tr]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(c j q, j), rfl⟩)

theorem exists_rep {A M O ι : Type} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι] [DecidableEq ι]
    (v : O → ι → M) (x : ι → M) (hx : ∀ j, x j ∈ Submodule.span A (Set.range fun p : O × ι => v p.1 p.2)) :
    ∃ (Q : Type) (_ : Fintype Q) (c : ι → ι → Q → O) (y : ι → ι → Q → A),
      ∀ j, x j = ∑ i, ∑ q, y i j q • v (c i j q) i := by
  choose n w gg hgg using fun j => Submodule.mem_span_set'.1 (hx j)
  choose pc hpc using fun j k => (gg j k).2
  refine ⟨Σ j', Fin (n j'), inferInstance, fun i j q => (pc q.1 q.2).1,
    fun i j q => if q.1 = j then (if (pc q.1 q.2).2 = i then w q.1 q.2 else 0) else 0, fun j => ?_⟩
  rw [Finset.sum_comm]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [hj']) (by simp)]
  rw [← hgg j]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [if_true, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ]
  rw [← hpc j k]

theorem conv_comb {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    (g : ↥(GK (ϖ.field a))) {Q : Type} [Fintype Q] (c : Q → O) (z : Q → Per.Acris l)
    (F : Q → ℕ → (ZMod a → S O K e)) (G : ℕ → (ZMod a → S O K e)) (hG : ∀ k, G k = ∑ q, c q • F q k)
    (r : ℕ) (hconv : ∀ q, ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣
      (1 : O) ⊗ₜ[ℤ_[l]] z q - ∑ k ∈ Finset.range n, ϖ.muDiv a O g k * ϖ.iC t K (F q k))
    (w : OCr l O) (hw : w = ∑ q, c q ⊗ₜ[ℤ_[l]] z q) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣
      w - ∑ k ∈ Finset.range n, ϖ.muDiv a O g k * ϖ.iC t K (G k) := by
  subst hw
  choose n₀ hn₀ using hconv
  refine ⟨Finset.univ.sup n₀, fun n hn => ?_⟩

  simp_rw [hG, map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro q _
  rw [← Finset.smul_sum, show c q ⊗ₜ[ℤ_[l]] z q = c q • ((1 : O) ⊗ₜ[ℤ_[l]] z q) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], ← smul_sub, Algebra.smul_def]
  exact Dvd.dvd.mul_left (hn₀ q n (le_trans (Finset.le_sup (Finset.mem_univ q)) hn)) _

theorem comb_S {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {a e : ℕ} {Q : Type} [Fintype Q] (c : Q → O) (w : ZMod a → Q → K⟦X⟧⟦X⟧)
    (G : ℕ → ZMod a → S O K e) (F : Q → ℕ → ZMod a → S O K e)
    (hG : ∀ k τ, (G k τ : K⟦X⟧) = (X : K⟦X⟧) ^ k * ((k.factorial : K⟦X⟧) * coeff k (∑ q, c q • w τ q)))
    (hF : ∀ q k τ, (F q k τ : K⟦X⟧) = (X : K⟦X⟧) ^ k * ((k.factorial : K⟦X⟧) * coeff k (w τ q))) :
    ∀ k, G k = ∑ q, c q • F q k := by
  intro k
  funext τ
  apply Subtype.ext

  rw [hG, Finset.sum_apply, AddSubmonoidClass.coe_finsetSum, map_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Pi.smul_apply, SetLike.val_smul, hF, PowerSeries.coeff_smul, mul_smul_comm, mul_smul_comm]



theorem galois_taylor_basis : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι), (X : (↥LL.1)⟦X⟧) ^ k * (P.mxInv τ *ᵥ (P.nabla ^ k) (P.phi (bas j)) τ) i ∈ S (↥(OL LL)) (↥LL.1) e) (g : ↥(GK (ϖ.field a))), ∃ Γ, (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)).IsLMat (g : GQ l) g Γ ∧ ∀ (i j : ι) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l ↥(OL LL)) ^ r ∣ toOCr l ↥(OL LL) (Γ i j) - ∑ k ∈ Finset.range n, ϖ.muDiv a ↥(OL LL) g k * ϖ.iC (thetaW a LL) ↥LL.1 (fun τ => ⟨_, hS τ j k i⟩) := by
  intro BS l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I hBK hS g
  letI := zlLat (resF T (ϖ.field a))
  obtain ⟨E, jA, hR, hIm⟩ := hBK
  have hO : ∀ c : ↥(OL LL), ∃ u : FHom E E, ∀ x, jA (u.u (ainfObj (ϖ.field a)) x) =
      (OfCrystal.mulZ (resF T (ϖ.field a)) c).lTensor (WCb l) (jA x) := fun c => by
    obtain ⟨u, hu, -⟩ := (BS l (ϖ.field a) (ainfObj (ϖ.field a)) (ainfId (ϖ.field a)) hR.ainf).2 _ _ _ _ E E jA jA hR hR
      (OfCrystal.mulZ (resF T (ϖ.field a)) c) fun g x => (((resF T (ϖ.field a)).actT g).map_smul c x).symm
    exact ⟨u, hu⟩
  choose oE hoE using hO
  obtain ⟨b, hb, hgen⟩ := GlobalTheory.T.breuilKisinPrism_crystal_basis_and_span l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE
  obtain ⟨sh, φ₂, hsh, hφC, hφsh⟩ := GlobalTheory.TaylorShift.shift_frob_exists l ↥LL.1
  obtain ⟨PP, S₀, p₀, p₁, δ, κ, κ₀, hPPI, hδ, hκ₀, hκp, hκφ, hSS, -, hev⟩ :=
    GlobalTheory.T.exists_crystalline_prisms l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ hl2 sh φ₂ hsh hφC hφsh
  obtain ⟨Q, _, c, y, hε⟩ := GlobalTheory.CrysGal.exists_rep (A := PP.A)
    (fun c i => (oE c).u PP (E.tr p₀ (b i))) (fun j => E.tr p₁ (b j))
    (fun j => GlobalTheory.CrysGal.mem_span_tr E p₀ oE b hgen _)
  have hF := GlobalTheory.T.crystal_changeOfBasis_frobenius_compat l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE b hb sh φ₂ hsh hφC PP p₀ p₁ κ hPPI hκp hκφ Q c y hε
  have hD := GlobalTheory.T.prismCrystal_changeOfBasis_constantCoeff_eq_one l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE b hb PP S₀ p₀ p₁ δ κ κ₀ hδ hκ₀ (fun τ x => (hκp τ x).1) Q c y hε
  have hK := GlobalTheory.T.frobeniusStratification_coeff_eq_connection_pow ↥(OL LL) ↥LL.1 l e a ι P sh φ₂ hsh hφC hφsh _ hD hF
  obtain ⟨Cr, eC, h, hCrI, heCφ, heCh⟩ := GlobalTheory.AcrisPrism.main l (ϖ.field a)
  have hev' := hev Cr eC h hCrI heCφ heCh g
  obtain ⟨ev, hevs⟩ := hev'
  have hG := GlobalTheory.T.galoisMatrix_eq_crystal_changeOfBasis_value l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE b hb PP p₀ p₁ Q c y hε Cr eC h heCh g ev hevs.1 hevs.2.1
  obtain ⟨Γ, hΓ, hΓeq⟩ := hG
  have hconv := hevs.2.2
  refine ⟨Γ, hΓ, fun i j r => ?_⟩
  have hG := GlobalTheory.CrysGal.comb_S (e := e) (c i j) (fun τ q => κ τ (y i j q))
    (fun k τ => ⟨_, hS τ j k i⟩) (fun q k τ => ⟨_, hSS τ (y i j q) k⟩)
    (fun k τ => (congrArg ((X : (↥LL.1)⟦X⟧) ^ k * ·) (hK τ k i j)).symm) (fun q k τ => rfl)
  exact GlobalTheory.CrysGal.conv_comb (thetaW a LL) ϖ g (c i j) (fun q => eC (ev.f (y i j q)))
    (fun q k τ => ⟨_, hSS τ (y i j q) k⟩) (fun k τ => ⟨_, hS τ j k i⟩) hG r (fun q => hconv (y i j q) r)
    _ (hΓeq i j)

end GlobalTheory.CrysGal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisDividedTaylorExpansionFrobeniusBasisStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galois_dividedTaylor_expansion_frobeniusBasis : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι), (X : (↥LL.1)⟦X⟧) ^ k * (P.mxInv τ *ᵥ (P.nabla ^ k) (P.phi (bas j)) τ) i ∈ S (↥(OL LL)) (↥LL.1) e) (g : ↥(GK (ϖ.field a))), ∃ Γ, (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)).IsLMat (g : GQ l) g Γ ∧ ∀ (i j : ι) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l ↥(OL LL)) ^ r ∣ toOCr l ↥(OL LL) (Γ i j) - ∑ k ∈ Finset.range n, ϖ.muDiv a ↥(OL LL) g k * ϖ.iC (thetaW a LL) ↥LL.1 (fun τ => ⟨_, hS τ j k i⟩) := by
  first | exact @GlobalTheory.CrysGal.galois_taylor_basis | exact GlobalTheory.CrysGal.galois_taylor_basis | (intros; apply GlobalTheory.CrysGal.galois_taylor_basis <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTaylorFormulaBreuilKisinLatticeStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galois_taylor_formula_breuilKisin_lattice : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : Lat a ↥(OL LL) ↥LL.1 ϖ) (I : Ident (thetaW a LL) ϖ P T) (C : Conn P) (hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι), (X : (↥LL.1)⟦X⟧) ^ k * (P.mxInv τ *ᵥ (C.nabla ^ k) (P.phi (bas j)) τ) i ∈ S (↥(OL LL)) (↥LL.1) e), (∀ g : ↥(GK (ϖ.field a)), ∃ Γ, I.IsLMat (g : GQ l) g Γ ∧ ∀ (i j : ι) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l ↥(OL LL)) ^ r ∣ toOCr l ↥(OL LL) (Γ i j) - ∑ k ∈ Finset.range n, ϖ.muDiv a ↥(OL LL) g k * ϖ.iC (thetaW a LL) ↥LL.1 (fun τ => ⟨_, hS τ j k i⟩)) → I.Taylor C := by
  first | exact @GlobalTheory.TaylorBasis.main | exact GlobalTheory.TaylorBasis.main | (intros; apply GlobalTheory.TaylorBasis.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralConnectionTaylorFormulaTameBreuilKisin

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.IntConnTaylor

theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∃ C : Conn P, C.nabla = P.nabla ∧ Ident.Taylor (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) C := by
  intro hBS l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I hBK
  obtain ⟨sh, φ₂, h1, h2, h3⟩ := GlobalTheory.T.exists_taylorShift_frobenius_twoVariable_compatible l (↥LL.1)
  obtain ⟨ε, hε0, hεφ, hεS⟩ := GlobalTheory.T.exists_integral_crystal_stratification_matrix hBS l a e ϖ LL hl2 ι P T I hBK sh φ₂ h1 h2 h3
  have hc := GlobalTheory.T.frobeniusStratification_coeff_eq_connection_pow (↥(OL LL)) (↥LL.1) l e a ι P sh φ₂ h1 h2 h3 ε hε0 hεφ
  have hphi : ∀ j, P.phi (bas j) ∈ P.MM := fun j =>
    P.ext_mono (fun _ h => A_le_S l e h) (P.phi_mem_L (P.bas_mem_M j))
  have hpow : ∀ (n : ℕ) (j : ι), (P.nabla ^ n) (P.phi (bas j)) ∈ P.MM := fun n j =>
    mem_tot.2 fun τ => P.mem_extc_iff.2 fun i => by rw [← hc τ n i j]; exact hεS τ i j n
  have hMM : ∀ m ∈ P.MM, P.nabla m ∈ P.MM := fun m hm =>
    P.nabla_mem_MM_of_basis (fun j => by simpa using hpow 1 j) hphi hm
  let C : Conn P := ⟨P.nabla, fun f v => P.nabla_smul_tot f v, hMM⟩
  have hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι), (X : (↥LL.1)⟦X⟧) ^ k *
      (P.mxInv τ *ᵥ (P.nabla ^ k) (P.phi (bas j)) τ) i ∈ S (↥(OL LL)) (↥LL.1) e := fun τ j k i =>
    mul_mem (pow_mem (uIn (S (↥(OL LL)) (↥LL.1) e)).2 k)
      (P.mem_extc_iff.1 (mem_tot.1 (hpow k j) τ) i)
  exact ⟨C, rfl, GlobalTheory.T.galois_taylor_formula_breuilKisin_lattice l a e ϖ LL hl2 ι P _ _ C hS (GlobalTheory.T.galois_dividedTaylor_expansion_frobeniusBasis hBS l a e ϖ LL hl2 ι P T I hBK hS)⟩

end GlobalTheory.IntConnTaylor
end
end
