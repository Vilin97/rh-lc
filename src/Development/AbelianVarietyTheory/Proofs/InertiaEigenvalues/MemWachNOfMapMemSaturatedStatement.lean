module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatOverProductPowerSeriesRingStatement
public import Mathlib.RingTheory.Flat.Basic
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAndDecompletion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemXSmulOfProjective
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachKernelMemFrobeniusSpanAfterQPowStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleUniquenessCharacterisationStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeComapOfExactFlat

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory

theorem isBaseChange_comap_of_exact (A E : Type) [CommRing A] [CommRing E] [Algebra A E]
    [Module.Flat A E] (D₀ D₁ D₂ : Type) [AddCommGroup D₀] [AddCommGroup D₁] [AddCommGroup D₂]
    [Module E D₀] [Module E D₁] [Module E D₂] [Module A D₀] [Module A D₁] [Module A D₂]
    [IsScalarTower A E D₀] [IsScalarTower A E D₁] [IsScalarTower A E D₂]
    (j : D₀ →ₗ[E] D₁) (q : D₁ →ₗ[E] D₂) (N₁ : Submodule A D₁) (N₂ : Submodule A D₂)
    (hj : Function.Injective j) (hex : Function.Exact j q) (_hq : Function.Surjective q)
    (h₁ : IsBaseChange E N₁.subtype) (h₂ : IsBaseChange E N₂.subtype)
    (hN : ∀ x ∈ N₁, q x ∈ N₂) :
    IsBaseChange E (N₁.comap (j.restrictScalars A)).subtype := by
  set N₀ := N₁.comap (j.restrictScalars A) with hN₀
  let ι : N₀ →ₗ[A] N₁ := (j.restrictScalars A).restrict (fun x hx => hx)
  let f : N₁ →ₗ[A] N₂ := (q.restrictScalars A).restrict hN
  have hιv : ∀ y : N₀, (ι y : D₁) = j y := fun _ => rfl
  have hfv : ∀ y : N₁, (f y : D₂) = q y := fun _ => rfl
  have hι : Function.Injective ι := by
    intro x y hxy
    apply Subtype.ext
    apply hj
    have := congrArg Subtype.val hxy
    simpa [ι] using this
  have hιf : Function.Exact ι f := by
    intro y
    constructor
    · intro hy
      have hy' : q (y : D₁) = 0 := by
        have := congrArg Subtype.val hy
        rwa [hfv] at this
      obtain ⟨x, hx⟩ := (hex (y : D₁)).1 hy'
      refine ⟨⟨x, ?_⟩, ?_⟩
      · show j x ∈ N₁
        rw [hx]; exact y.2
      · apply Subtype.ext
        simpa [ι] using hx
    · rintro ⟨x, rfl⟩
      apply Subtype.ext
      simp only [f, ι, LinearMap.restrict_apply, LinearMap.restrictScalars_apply,
        ZeroMemClass.coe_zero]
      exact (hex (j x)).2 ⟨x, rfl⟩
  have hιT : Function.Injective (LinearMap.lTensor E ι) :=
    Module.Flat.lTensor_preserves_injective_linearMap ι hι
  have hfT : Function.Exact (LinearMap.lTensor E ι) (LinearMap.lTensor E f) :=
    Module.Flat.lTensor_exact E hιf
  let Φ : E ⊗[A] N₀ →ₗ[E] D₀ := N₀.subtype.liftBaseChange E
  have hcomm₁ : ∀ t : E ⊗[A] N₀, j (Φ t) = h₁.equiv (LinearMap.lTensor E ι t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [Φ, IsBaseChange.equiv_tmul, hιv]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hcomm₂ : ∀ t : E ⊗[A] N₁, h₂.equiv (LinearMap.lTensor E f t) = q (h₁.equiv t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [IsBaseChange.equiv_tmul, hfv]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hΦi : Function.Injective Φ := by
    intro s t hst
    apply hιT
    apply h₁.equiv.injective
    rw [← hcomm₁, ← hcomm₁, hst]
  have hΦs : Function.Surjective Φ := by
    intro d
    obtain ⟨t, ht⟩ := h₁.equiv.surjective (j d)
    have h0 : LinearMap.lTensor E f t = 0 := by
      apply h₂.equiv.injective
      rw [hcomm₂, ht, map_zero]
      exact (hex (j d)).2 ⟨d, rfl⟩
    obtain ⟨s, hs⟩ := (hfT t).1 h0
    refine ⟨s, hj ?_⟩
    rw [hcomm₁, hs, ht]
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective Φ ⟨hΦi, hΦs⟩) ?_
  intro x
  show Φ (1 ⊗ₜ x) = x
  simp [Φ, LinearMap.liftBaseChange_tmul]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeComapOfExactFlatStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.isBaseChange_comap_of_exact_flat : ∀ (A E : Type) [CommRing A] [CommRing E] [Algebra A E] [Module.Flat A E] (D₀ D₁ D₂ : Type) [AddCommGroup D₀] [AddCommGroup D₁] [AddCommGroup D₂] [Module E D₀] [Module E D₁] [Module E D₂] [Module A D₀] [Module A D₁] [Module A D₂] [IsScalarTower A E D₀] [IsScalarTower A E D₁] [IsScalarTower A E D₂] (j : D₀ →ₗ[E] D₁) (q : D₁ →ₗ[E] D₂) (N₁ : Submodule A D₁) (N₂ : Submodule A D₂), Function.Injective j → Function.Exact j q → Function.Surjective q → IsBaseChange E N₁.subtype → IsBaseChange E N₂.subtype → (∀ x ∈ N₁, q x ∈ N₂) → IsBaseChange E (N₁.comap (j.restrictScalars A)).subtype := by
  first | exact @GlobalTheory.isBaseChange_comap_of_exact | exact GlobalTheory.isBaseChange_comap_of_exact | (intros; apply GlobalTheory.isBaseChange_comap_of_exact <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachKernelIntersectionFreeOfBaseChange

section

@[expose] public section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.WachKernel



theorem kernel_freeA : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → IsBaseChange W.EE ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))).subtype → FreeA W T₀ ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))) := by
  intro D HW F l _ K s LL h W T₀ T₁ T₂ ι π h0 h1 h2 hses hbc
  have hexact : Function.Injective (W.map ι) ∧ Function.Exact (W.map ι) (W.map π) ∧
      Function.Surjective (W.map π) :=
    GlobalTheory.EtaleExact.DD_exact D HW F
      (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h T₀ T₁ T₂ ι π hses
  obtain ⟨hinj, hex, -⟩ := hexact
  obtain ⟨_, -, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hproj := (HW l).W_proj K s LL h T₁
  set N₀ := (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)) with hN₀
  haveI : Module.Free W.EE (W.DD T₀) := (W.DD_free T₀).1
  haveI : IsNoetherianRing ↥(OL LL) := inferInstance
  haveI : IsNoetherianRing (PowerSeries ↥(OL LL)) := inferInstance
  haveI : IsNoetherianRing (AA K LL) :=
    inferInstanceAs (IsNoetherianRing (ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)))
  haveI : Module.Finite (AA K LL) ↥(W.N T₁) := Module.Finite.iff_fg.mpr (W.N_fg T₁)
  have hfin : Module.Finite (AA K LL) ↥N₀ := by
    let g : ↥N₀ →ₗ[AA K LL] ↥(W.N T₁) :=
      ((W.map ι).restrictScalars (AA K LL)).restrict (fun x hx => hx)
    haveI : IsNoetherian (AA K LL) ↥(W.N T₁) := isNoetherian_of_isNoetherianRing_of_finite _ _
    exact Module.Finite.of_injective g fun a b hab =>
      Subtype.ext (hinj (congrArg Subtype.val hab))
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
    simp [(Fact.out : l.Prime).ne_zero] at this
  have hX : IsSMulRegular ↥N₀ (fun _ => X : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)) := by
    intro x y hxy
    have h1 : (letπ : AA K LL) • (x : W.DD T₀) = (letπ : AA K LL) • (y : W.DD T₀) :=
      congrArg Subtype.val hxy
    rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE letπ (y : W.DD T₀)] at h1
    exact Subtype.ext (W.EE_π.smul_left_cancel.mp h1)
  have hreg : ∀ x y : ↥N₀,
      (fun _ => C ((l : ℕ) : ↥(OL LL)) : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)) • x =
        (fun _ => X : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)) • y →
      ∃ z : ↥N₀, x = (fun _ => X : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)) • z := by
    intro x y hxy
    have hinj : Function.Injective (W.map ι) := hinj
    have hex : Function.Exact (W.map ι) (W.map π) := hex
    let mA := (W.map ι).restrictScalars (AA K LL)
    let x' : ↥(W.N T₁) := ⟨mA x, x.2⟩
    let y' : ↥(W.N T₁) := ⟨mA y, y.2⟩
    have hxy' : (fun _ => C ((l : ℕ) : ↥(OL LL)) : AA K LL) • x' = (fun _ => X : AA K LL) • y' := by
      apply Subtype.ext
      have := congrArg (fun w : ↥N₀ => mA (w : W.DD T₀)) hxy
      simpa only [Submodule.coe_smul, map_smul] using this
    have e1 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (C ((l : ℕ) : ℤ_[l])) =
        fun _ => C ((l : ℕ) : ↥(OL LL)) := by
      funext i
      simp
    have e2 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X = fun _ => X := by
      funext i
      simp [zlA]
    obtain ⟨z, hz⟩ := @GlobalTheory.WachFree.mem_X_smul_of_projective ℤ_[l] ↥(W.N T₁) _ _ _
      (Module.compHom _ (zlA LL (Module.finrank ℚ_[l] ↥(K0 K)))) hproj ((l : ℕ) : ℤ_[l])
      (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) x' y' (by
        change zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (C ((l : ℕ) : ℤ_[l])) • x' =
          zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X • y'
        rw [e1, e2]
        exact hxy')
    change x' = zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X • z at hz
    rw [e2] at hz
    have hz' : mA x = (fun _ => X : AA K LL) • (z : W.DD T₁) := congrArg Subtype.val hz
    have hπz : W.map π (z : W.DD T₁) = 0 := by
      have h0 : W.map π (mA x) = 0 := (hex _).mpr ⟨(x : W.DD T₀), rfl⟩
      rw [hz'] at h0
      have h0' : (letπ : AA K LL) • W.map π (z : W.DD T₁) = (letπ : AA K LL) • 0 := by
        rw [smul_zero]
        have : W.map π ((letπ : AA K LL) • (z : W.DD T₁)) = (letπ : AA K LL) • W.map π (z : W.DD T₁) :=
          ((W.map π).restrictScalars (AA K LL)).map_smul _ _
        rw [← this]
        exact h0
      rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE letπ (0 : W.DD T₂)] at h0'
      exact W.EE_π.smul_left_cancel.mp h0'
    obtain ⟨w, hw⟩ := (hex (z : W.DD T₁)).mp hπz
    have hwN : w ∈ N₀ := by
      show W.map ι w ∈ W.N T₁
      rw [hw]
      exact z.2
    refine ⟨⟨w, hwN⟩, Subtype.ext (hinj ?_)⟩
    change mA x = W.map ι ((fun _ => X : AA K LL) • w)
    rw [hz', ← hw]
    exact (mA.map_smul _ _).symm
  obtain ⟨b⟩ := GlobalTheory.WachFree.basis_of_regular (ι := ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    (O := ↥(OL LL)) (N := ↥N₀) (E := W.EE) (D := W.DD T₀) W.EE_inj N₀.subtype hbc
    ((l : ℕ) : ↥(OL LL)) hl0 hl hX hreg
  refine ⟨Module.finrank W.EE (W.DD T₀), fun j => (b j : W.DD T₀), fun j => (b j).2, fun x hx => ?_⟩
  refine ⟨fun j => b.repr ⟨x, hx⟩ j, ?_, ?_⟩
  · have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using this.symm
  · intro a ha
    have hx' : (⟨x, hx⟩ : ↥N₀) = ∑ j, a j • b j :=
      Subtype.ext (by simpa only [Submodule.coe_sum, Submodule.coe_smul] using ha)
    funext j
    rw [hx', b.repr_sum_self]

end GlobalTheory.WachKernel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachKernelIntersectionFreeOfBaseChangeStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.wachKernel_intersection_free_of_baseChange : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → IsBaseChange W.EE ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))).subtype → FreeA W T₀ ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))) := by
  first | exact @GlobalTheory.WachKernel.kernel_freeA | exact GlobalTheory.WachKernel.kernel_freeA | (intros; apply GlobalTheory.WachKernel.kernel_freeA <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachNOfMapMemSaturated

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.KerSat



theorem mem_N_of_map_mem : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∀ x : W.DD T₀, W.map ι x ∈ W.N T₁ → x ∈ W.N T₀ := by
  intro D HW F l _ K s LL h W E T₀ T₁ T₂ ι π h0 h1 h2 hses x hx
  have hex : Function.Injective (W.map ι) ∧ Function.Exact (W.map ι) (W.map π) ∧
      Function.Surjective (W.map π) := by
    haveI := GlobalTheory.EtaleExact.finite_OL LL
    haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
    refine GlobalTheory.EtaleExact.exact_of_tie E (GlobalTheory.EtaleExact.map_ne_top_of_tie E ?_ ?_) T₀ T₁ T₂ ι π hses
    · rw [(D.loc l).PD_p K]
      exact GlobalTheory.EtaleExact.isUnit_or_dvd_pow (D.loc l) LL
    · rw [(D.loc l).PD_p K]
      exact GlobalTheory.EtaleExact.sep_RW LL
  have key := GlobalTheory.T.wachModule_uniqueness_characterisation D HW F l K s LL h T₀ h0
  obtain ⟨hinj, hexact, hsurj⟩ : Function.Injective (W.map ι) ∧ Function.Exact (W.map ι) (W.map π) ∧
      Function.Surjective (W.map π) := hex
  haveI := GlobalTheory.EtaleExact.finite_OL LL
  haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
  haveI := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  haveI : Module.Flat (AA K LL) W.EE :=
    GlobalTheory.T.flat_over_product_power_series_ring _ _ W.EE ((D.loc l).PD K).p W.EE_π W.EE_complete W.EE_dense W.EE_sat
  have hbc : IsBaseChange W.EE ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))).subtype :=
    GlobalTheory.T.isBaseChange_comap_of_exact_flat (AA K LL) W.EE _ _ _ (W.map ι) (W.map π) (W.N T₁) (W.N T₂) hinj hexact hsurj
      (W.N_base T₁ h1) (W.N_base T₂ h2) (fun y hy => W.map_N π h1 h2 y hy)
  have hcomp : ∀ z, W.map π (W.map ι z) = 0 := fun z => (hexact _).2 ⟨z, rfl⟩
  have hA : ∀ (a : AA K LL) (z : W.DD T₀), W.map ι (a • z) = a • W.map ι z := fun a z =>
    ((W.map ι).restrictScalars (AA K LL)).map_smul a z
  have hAπ : ∀ (a : AA K LL) (z : W.DD T₁), W.map π (a • z) = a • W.map π z := fun a z =>
    ((W.map π).restrictScalars (AA K LL)).map_smul a z
  have hπc : ∀ y : W.DD T₁, W.map π ((letπ : AA K LL) • y) = 0 → W.map π y = 0 := by
    intro y hy
    rw [hAπ, ← algebraMap_smul W.EE (letπ : AA K LL)] at hy
    exact (W.EE_π.smul_left_cancel).mp (hy.trans (smul_zero _).symm)
  have hγ : ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), W.γ T₀ y ∈
      (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)) := by
    intro y hy
    show W.map ι (W.γD T₀ W.gam y) ∈ W.N T₁
    rw [W.map_γ]
    exact W.N_Γ T₁ W.gam _ hy
  have hγπ : ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), W.γ T₀ y - y ∈
      ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))).map (smulA W T₀ letπ) := by
    intro y hy
    change W.map ι y ∈ W.N T₁ at hy
    obtain ⟨z, hz, hzeq⟩ := W.N_π T₁ W.gam _ hy
    have h3 : W.map π z = 0 := by
      apply hπc
      rw [← hzeq, map_sub, W.map_γ, hcomp, map_zero, sub_zero]
    obtain ⟨z₀, rfl⟩ := (hexact z).1 h3
    refine ⟨z₀, hz, ?_⟩
    apply hinj
    change W.map ι ((letπ : AA K LL) • z₀) = W.map ι (W.γD T₀ W.gam y - y)
    rw [hA, map_sub, W.map_γ, hzeq]
  have hφ : ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), ∃ k : ℕ, W.Q ^ k • W.φD T₀ y ∈
      (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)) := by
    intro y hy
    obtain ⟨k, hk⟩ := W.N_φ T₁ _ hy
    refine ⟨k, ?_⟩
    show W.map ι (W.Q ^ k • W.φD T₀ y) ∈ W.N T₁
    rw [hA, W.map_φ]
    exact hk
  have hfree := GlobalTheory.T.wachKernel_intersection_free_of_baseChange D HW F l K s LL h T₀ T₁ T₂ ι π h0 h1 h2 hses hbc
  have hspan := GlobalTheory.T.wachKernel_mem_frobeniusSpan_after_Q_pow D HW F l K s LL h T₀ T₁ T₂ ι π h0 h1 h2 hses
  have heq := key _ hfree hbc hγ hγπ hφ hspan
  rw [← heq]
  exact hx

end GlobalTheory.NL.KerSat
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachNOfMapMemSaturatedStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.mem_wachN_of_map_mem_saturated : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∀ x : W.DD T₀, W.map ι x ∈ W.N T₁ → x ∈ W.N T₀ := by
  first | exact @GlobalTheory.NL.KerSat.mem_N_of_map_mem | exact GlobalTheory.NL.KerSat.mem_N_of_map_mem | (intros; apply GlobalTheory.NL.KerSat.mem_N_of_map_mem <;> assumption)
end
end
