module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitCoeffWittTiltRelationStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthCokerOfSurjectiveModUniformizerStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiModuleHomShortExactSplitWittTilt

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory

theorem phiModuleHom_shortExact_split_wittTilt {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {G : Type}
    [Group G] [TopologicalSpace G] {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ] {P₀ : PhiMod O K l e a ι} {P₁ : PhiMod O K l e a κ} {P₂ : PhiMod O K l e a μ}
    {T₀ T₁ T₂ : LocLat G ℚ_[l] K O} {I₀ : Ident t ϖ P₀ T₀} {I₁ : Ident t ϖ P₁ T₁} {I₂ : Ident t ϖ P₂ T₂}
    {f : LatHom T₀.L T₁.L} {g : LatHom T₁.L T₂.L} {F : GlobalTheory.BK.Hom P₀ P₁} {H : GlobalTheory.BK.Hom P₁ P₂}
    (hS : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I₀ I₁ f F) (hH : IsMapOf I₁ I₂ g H) :
    (∃ Z : Matrix κ μ (OW l O), (homMat t ϖ H).map (inclO l O) * Z = 1) ∧
      (∃ Y : Matrix ι κ (OW l O), Y * (homMat t ϖ F).map (inclO l O) = 1) := by
  classical

  let g₁ : ↥T₁.L.T →ₗ[O] ↥T₂.L.T := (g.f.restrictScalars O).restrict g.T_le
  let f₁ : ↥T₀.L.T →ₗ[O] ↥T₁.L.T := (f.f.restrictScalars O).restrict f.T_le
  have hg₁s : Function.Surjective g₁ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := hS.2.2.1 y hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  haveI : Module.Free O ↥T₂.L.T := T₂.L.free
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g₁ LinearMap.id hg₁s
  have hs' : ∀ y, g₁ (s y) = y := fun y => LinearMap.congr_fun hs y
  have hf₁i : Function.Injective f₁ := fun x y h => Subtype.ext (hS.1 (congrArg Subtype.val h))
  have hgf : ∀ y, g₁ (f₁ y) = 0 := fun y => Subtype.ext ((hS.2.2.2.1 _).2 ⟨y, rfl⟩)
  let p : ↥T₁.L.T →ₗ[O] ↥T₁.L.T := LinearMap.id - s ∘ₗ g₁
  have hp : ∀ x, p x ∈ LinearMap.range f₁ := by
    intro x
    have h0 : g₁ (p x) = 0 := by
      simp only [p, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hs', sub_self]
    obtain ⟨y, hy⟩ := (hS.2.2.2.1 _).1 (congrArg Subtype.val h0)
    have hy0 : y ∈ T₀.L.T := hS.2.2.2.2 y (hy ▸ (p x).2)
    exact ⟨⟨y, hy0⟩, Subtype.ext hy⟩
  let r : ↥T₁.L.T →ₗ[O] ↥T₀.L.T :=
    (LinearEquiv.ofInjective f₁ hf₁i).symm.toLinearMap ∘ₗ p.codRestrict (LinearMap.range f₁) hp
  have hr : ∀ y, r (f₁ y) = y := by
    intro y
    have h1 : p.codRestrict (LinearMap.range f₁) hp (f₁ y) = LinearEquiv.ofInjective f₁ hf₁i y := by
      apply Subtype.ext
      simp [p, hgf]
    simp only [r, LinearMap.comp_apply, h1, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

  let Sw := s.baseChange (OW l O)
  let Rw := r.baseChange (OW l O)
  have hSw : ∀ x, latW g (Sw x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c y =>
      simp only [Sw, LinearMap.baseChange_tmul, latW, TensorProduct.map_tmul, LinearMap.id_apply]
      exact congrArg _ (hs' y)
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hRw : ∀ x, Rw (latW f x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c y =>
      simp only [Rw, LinearMap.baseChange_tmul, latW, TensorProduct.map_tmul, LinearMap.id_apply]
      exact congrArg _ (hr y)
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

  let SL : (μ → OW l O) →ₗ[OW l O] (κ → OW l O) := I₁.j.symm.toLinearMap ∘ₗ Sw ∘ₗ I₂.j.toLinearMap
  let RL : (κ → OW l O) →ₗ[OW l O] (ι → OW l O) := I₀.j.symm.toLinearMap ∘ₗ Rw ∘ₗ I₁.j.toLinearMap
  have hSL : homW t ϖ H ∘ₗ SL = LinearMap.id := by
    refine LinearMap.ext fun v => I₂.j.injective ?_
    rw [LinearMap.comp_apply, hH]
    simp only [SL, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hSw,
      LinearMap.id_apply]
  have hRL : RL ∘ₗ homW t ϖ F = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    change I₀.j.symm (Rw (I₁.j (homW t ϖ F v))) = v
    rw [hF, hRw, LinearEquiv.symm_apply_apply]
  have hM : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (M : Matrix α β (OW l O)), LinearMap.toMatrix' M.mulVecLin = M := fun M => LinearMap.toMatrix'_toLin' M
  refine ⟨⟨LinearMap.toMatrix' SL, ?_⟩, ⟨LinearMap.toMatrix' RL, ?_⟩⟩
  · have h := congrArg LinearMap.toMatrix' hSL
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at h
    rw [← h, homW, hM]
  · have h := congrArg LinearMap.toMatrix' hRL
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at h
    rw [← h, homW, hM]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiModuleHomShortExactSplitWittTiltStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.phiModuleHom_shortExact_split_wittTilt_alt : ∀ {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {G : Type} [Group G] [TopologicalSpace G] {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] {P₀ : PhiMod O K l e a ι} {P₁ : PhiMod O K l e a κ} {P₂ : PhiMod O K l e a μ} {T₀ T₁ T₂ : LocLat G ℚ_[l] K O} {I₀ : Ident t ϖ P₀ T₀} {I₁ : Ident t ϖ P₁ T₁} {I₂ : Ident t ϖ P₂ T₂} {f : LatHom T₀.L T₁.L} {g : LatHom T₁.L T₂.L} {F : GlobalTheory.BK.Hom P₀ P₁} {H : GlobalTheory.BK.Hom P₁ P₂} (hS : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I₀ I₁ f F) (hH : IsMapOf I₁ I₂ g H), (∃ Z : Matrix κ μ (OW l O), (homMat t ϖ H).map (inclO l O) * Z = 1) ∧ (∃ Y : Matrix ι κ (OW l O), Y * (homMat t ϖ F).map (inclO l O) = 1) := by
  first | exact @GlobalTheory.phiModuleHom_shortExact_split_wittTilt | exact GlobalTheory.phiModuleHom_shortExact_split_wittTilt | (intros; apply GlobalTheory.phiModuleHom_shortExact_split_wittTilt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSettingGroupActionCompat

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKReal.SESExact

theorem homW_exact_middle : ∀ {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {G : Type} [Group G] [TopologicalSpace G] {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] {P₀ : PhiMod O K l e a ι} {P₁ : PhiMod O K l e a κ} {P₂ : PhiMod O K l e a μ} {T₀ T₁ T₂ : LocLat G ℚ_[l] K O} {I₀ : Ident t ϖ P₀ T₀} {I₁ : Ident t ϖ P₁ T₁} {I₂ : Ident t ϖ P₂ T₂} {f : LatHom T₀.L T₁.L} {g : LatHom T₁.L T₂.L} {F : GlobalTheory.BK.Hom P₀ P₁} {H : GlobalTheory.BK.Hom P₁ P₂} (hS : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I₀ I₁ f F) (hH : IsMapOf I₁ I₂ g H), ∀ v : κ → OW l O, homW t ϖ H v = 0 → ∃ w, homW t ϖ F w = v := by
  intro l _ a _ e _ O K _ _ _ _ _ _ _ _ _ t ϖ G _ _ ι κ μ _ _ _ _ _ _ P₀ P₁ P₂ T₀ T₁ T₂ I₀ I₁ I₂ f g F H hS hF hH v hv
  obtain ⟨-, -, hOnto, hker, hsat⟩ := hS
  set f₁ := (f.f.restrictScalars O).restrict f.T_le with hf₁
  set g₁ := (g.f.restrictScalars O).restrict g.T_le with hg₁
  have hgs : Function.Surjective g₁ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := hOnto y hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hex : Function.Exact f₁ g₁ := by
    rintro ⟨y, hy⟩
    constructor
    · intro h0
      have h0' : g.f y = 0 := congrArg Subtype.val h0
      obtain ⟨z, hz⟩ := (hker y).1 h0'
      have hzT : z ∈ T₀.L.T := hsat z (hz ▸ hy)
      exact ⟨⟨z, hzT⟩, Subtype.ext hz⟩
    · rintro ⟨⟨z, hzT⟩, hz⟩
      apply Subtype.ext
      have hz' : f.f z = y := congrArg Subtype.val hz
      exact (hker y).2 ⟨z, hz'⟩
  have hT := lTensor_exact (OW l O) hex hgs
  have h1 : latW g (I₁.j v) = 0 := by
    rw [← hH v, hv, map_zero]
  obtain ⟨z, hz⟩ := (hT (I₁.j v)).1 h1
  refine ⟨I₀.j.symm z, I₁.j.injective ?_⟩
  rw [hF, LinearEquiv.apply_symm_apply]
  exact hz

end GlobalTheory.BKReal.SESExact
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSettingGroupActionCompatStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.tame_setting_group_action_compat : ∀ {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {G : Type} [Group G] [TopologicalSpace G] {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] {P₀ : PhiMod O K l e a ι} {P₁ : PhiMod O K l e a κ} {P₂ : PhiMod O K l e a μ} {T₀ T₁ T₂ : LocLat G ℚ_[l] K O} {I₀ : Ident t ϖ P₀ T₀} {I₁ : Ident t ϖ P₁ T₁} {I₂ : Ident t ϖ P₂ T₂} {f : LatHom T₀.L T₁.L} {g : LatHom T₁.L T₂.L} {F : GlobalTheory.BK.Hom P₀ P₁} {H : GlobalTheory.BK.Hom P₁ P₂} (hS : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I₀ I₁ f F) (hH : IsMapOf I₁ I₂ g H), ∀ v : κ → OW l O, homW t ϖ H v = 0 → ∃ w, homW t ϖ F w = v := by
  first | exact @GlobalTheory.BKReal.SESExact.homW_exact_middle | exact GlobalTheory.BKReal.SESExact.homW_exact_middle | (intros; apply GlobalTheory.BKReal.SESExact.homW_exact_middle <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsExactTripleBreuilKisinOfShortExactLattices

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKExact

theorem det_mul_eq_sum_fun' {R : Type*} [CommRing R] {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m]
    [DecidableEq m] (A : Matrix ι m R) (B : Matrix m ι R) :
    (A * B).det = ∑ f : ι → m, (∏ β, B (f β) β) * (A.submatrix id f).det := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_
  simp only [Finset.prod_mul_distrib, Matrix.submatrix_apply, id]
  ring

def selCols {R : Type*} [CommRing R] {m n : Type*} [DecidableEq n] (s : m → n) : Matrix n m R :=
  fun k i => if s i = k then (1 : R) else 0

theorem mul_selCols {R : Type*} [CommRing R] {m n : Type*} [Fintype n] [DecidableEq n] (N : Matrix m n R)
    (s : m → n) : N * (selCols (R := R) s) = N.submatrix id s := by
  ext i j
  rw [Matrix.mul_apply]
  simp [selCols]

theorem exists_right_of_minor {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (N : Matrix m n (A O K)) (s : m → n) :
    ∃ Y : Matrix n m K⟦X⟧, (∀ i j, Y i j ∈ A O K) ∧
      N.map (A O K).val * Y = ((N.submatrix id s).det : K⟦X⟧) • (1 : Matrix m m K⟦X⟧) := by
  refine ⟨(selCols (R := A O K) s * (N.submatrix id s).adjugate).map (A O K).val, fun i j => (_ : A O K).2, ?_⟩
  have h1 : N.map (A O K).val * (selCols (R := A O K) s * (N.submatrix id s).adjugate).map (A O K).val =
      (N * (selCols (R := A O K) s * (N.submatrix id s).adjugate)).map (A O K).val := by
    simp only [Matrix.map_mul]
  rw [h1, ← Matrix.mul_assoc, mul_selCols, Matrix.mul_adjugate]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem exists_right {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (M : Matrix m n (ZMod a → A O K))
    (Z : Matrix n m (OW l O)) (hZ : M.map (fun x => inclO l O (ϖ.iTot t K x)) * Z = 1) (τ : ZMod a) :
    ∃ (Y : Matrix n m K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ g ∈ A O K ∧ (∃ k, ‖coeff k g‖ = 1) ∧
      (Matrix.of fun i j => (M i j τ : K⟦X⟧)) * Y = g • (1 : Matrix m m K⟦X⟧) := by
  let φ : (ZMod a → A O K) →+* OW l O := (inclO l O).toRingHom.comp (ϖ.iTot t K).toRingHom
  have h1 := congrArg Matrix.det hZ
  rw [Matrix.det_one, det_mul_eq_sum_fun'] at h1
  have h2 : ∀ f : m → n, ((M.map fun x => inclO l O (ϖ.iTot t K x)).submatrix id f).det =
      inclO l O (ϖ.iTot t K (M.submatrix id f).det) := fun f => by
    exact (RingHom.map_det φ (M.submatrix id f)).symm
  simp only [h2] at h1
  obtain ⟨f, k, hk⟩ := GlobalTheory.T.exists_unit_coeff_wittTilt_relation t ϖ (fun f => (M.submatrix id f).det) _ h1 τ
  let N : Matrix m n (A O K) := fun i j => M i j τ
  have h3 : (M.submatrix id f).det τ = (N.submatrix id f).det :=
    RingHom.map_det (Pi.evalRingHom (fun _ : ZMod a => A O K) τ) (M.submatrix id f)
  obtain ⟨Y, hY, hNY⟩ := exists_right_of_minor N f
  refine ⟨Y, _, hY, (N.submatrix id f).det.2, ⟨k, ?_⟩, hNY⟩
  rw [← h3]
  exact hk

theorem isExactTriple_of_isSESLat_gen {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {G : Type} [Group G] [TopologicalSpace G]
    {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]
    {P₀ : PhiMod O K l e a ι} {P₁ : PhiMod O K l e a κ} {P₂ : PhiMod O K l e a μ}
    {T₀ T₁ T₂ : LocLat G ℚ_[l] K O} {I₀ : Ident t ϖ P₀ T₀} {I₁ : Ident t ϖ P₁ T₁} {I₂ : Ident t ϖ P₂ T₂}
    {f : LatHom T₀.L T₁.L} {g : LatHom T₁.L T₂.L} {F : BK.Hom P₀ P₁} {H : BK.Hom P₁ P₂}
    (hS : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I₀ I₁ f F) (hH : IsMapOf I₁ I₂ g H) : IsExactTriple F H := by
  obtain ⟨⟨Z, hZ⟩, ⟨Yw, hYw⟩⟩ := GlobalTheory.T.phiModuleHom_shortExact_split_wittTilt_alt t ϖ hS hF hH
  have hex := GlobalTheory.T.tame_setting_group_action_compat t ϖ hS hF hH
  let φ : (ZMod a → A O K) →+* OW l O := (inclO l O).toRingHom.comp (ϖ.iTot t K).toRingHom
  have hφ : Function.Injective φ := inclO_injective.comp (ϖ.iTot_injective t K)
  let ψ : ZMod a → (ZMod a → A O K) →+* K⟦X⟧ := fun τ =>
    (A O K).val.toRingHom.comp (Pi.evalRingHom (fun _ : ZMod a => A O K) τ)
  have extPi : ∀ {m n : Type} (M N : Matrix m n (ZMod a → A O K)),
      (∀ τ, M.map (ψ τ) = N.map (ψ τ)) → M = N := fun M N h => by
    funext i j τ
    exact Subtype.ext (congrFun₂ (h τ) i j)
  let Ht : Matrix μ κ (ZMod a → A O K) := fun i j τ => ⟨H.mat τ i j, H.mem τ i j⟩
  let Ft : Matrix κ ι (ZMod a → A O K) := fun i j τ => ⟨F.mat τ i j, F.mem τ i j⟩
  have hHr : ∀ τ, ∃ (Y : Matrix κ μ K⟦X⟧) (c : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧
      c ∈ A O K ∧ (∃ k, ‖coeff k c‖ = 1) ∧ H.mat τ * Y = c • (1 : Matrix μ μ K⟦X⟧) :=
    fun τ => exists_right t ϖ Ht Z hZ τ
  have hFl : ∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (c : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧
      c ∈ A O K ∧ (∃ k, ‖coeff k c‖ = 1) ∧ Y * F.mat τ = c • (1 : Matrix ι ι K⟦X⟧) := by
    intro τ
    have hT : Ftᵀ.map (fun x => inclO l O (ϖ.iTot t K x)) * Ywᵀ = 1 := by
      rw [Matrix.transpose_map, ← Matrix.transpose_mul]
      exact (congrArg Matrix.transpose hYw).trans Matrix.transpose_one
    obtain ⟨Y, c, hY, hc, hk, h⟩ := exists_right t ϖ Ftᵀ Ywᵀ hT τ
    refine ⟨Yᵀ, c, fun i j => hY j i, hc, hk, ?_⟩
    have h1 := congrArg Matrix.transpose h
    rw [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_one] at h1
    exact h1
  choose YH cH hYH hcH hkH hHY using hHr
  choose YF cF hYF hcF hkF hFY using hFl
  have hne : ∀ {c : K⟦X⟧}, (∃ k, ‖coeff k c‖ = 1) → c ≠ 0 := by
    rintro c ⟨k, hk⟩ rfl
    simp at hk
  refine ⟨?_, ?_, ?_⟩
  · intro v hv hFv
    funext τ
    have h1 : cF τ • v τ = 0 := by
      have h2 := congrArg (fun x => YF τ *ᵥ x τ) hFv
      simp only [Hom.app_apply, Matrix.mulVec_mulVec, hFY, Matrix.smul_mulVec, Matrix.one_mulVec,
        Pi.zero_apply, Matrix.mulVec_zero] at h2
      exact h2
    exact (smul_eq_zero.1 h1).resolve_left (hne (hkF τ))
  · intro v hv
    constructor
    · intro hHv
      refine (GlobalTheory.T.finiteLength_coker_of_surjective_mod_uniformizer O K l e a ι κ P₀ P₁ F).2 (fun τ => ⟨YF τ, cF τ, hYF τ, hkF τ, hFY τ⟩) v hv
        (∏ τ, cF τ) (prod_mem fun τ _ => hcF τ) (Finset.prod_ne_zero_iff.2 fun τ _ => hne (hkF τ)) ?_
      let Yt : Matrix ι κ (ZMod a → A O K) := fun i j τ => ⟨YF τ i j, hYF τ i j⟩
      let gt : ZMod a → A O K := fun τ => ⟨cF τ, hcF τ⟩
      let vt : κ → ZMod a → A O K := fun i τ => ⟨v τ i, mem_tot.1 hv τ i⟩
      have hYFt : Yt * Ft = Matrix.diagonal fun _ => gt := by
        refine extPi _ _ fun τ => ?_
        rw [Matrix.map_mul, Matrix.diagonal_map (map_zero _)]
        exact (hFY τ).trans (Matrix.smul_one_eq_diagonal _)
      have hv' : toW t ϖ P₁ ⟨v, mem_ME_of_mem_M hv⟩ = fun i => φ (vt i) :=
        funext fun i => ϖ.iW_of_mem t K (vt i)
      have h0 : homW t ϖ H (toW t ϖ P₁ ⟨v, mem_ME_of_mem_M hv⟩) = 0 := by
        rw [homW_toW]
        have : (⟨H.app v, H.app_mem_Mext (le_away _ _) (mem_ME_of_mem_M hv)⟩ : ME P₂) = 0 :=
          Subtype.ext hHv
        rw [this, map_zero]
      obtain ⟨w, hw⟩ := hex _ h0
      rw [homW_apply, hv'] at hw
      change Ft.map φ *ᵥ w = fun i => φ (vt i) at hw
      have h1 : (Ft * Yt).map φ *ᵥ (fun i => φ (vt i)) = φ gt • (fun i => φ (vt i)) := by
        rw [← hw, Matrix.map_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc,
          show Yt.map φ * Ft.map φ = (Yt * Ft).map φ from (Matrix.map_mul).symm, hYFt,
          Matrix.diagonal_map (map_zero _), ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
          Matrix.smul_mulVec]
      have h2 : (Ft * Yt) *ᵥ vt = gt • vt := by
        funext i
        apply hφ
        rw [RingHom.map_mulVec]
        refine (congrFun h1 i).trans ?_
        show φ gt * φ (vt i) = φ (gt * vt i)
        rw [map_mul]
      have hkey : ∀ τ, F.mat τ *ᵥ (YF τ *ᵥ v τ) = cF τ • v τ := fun τ => by
        funext i
        have := congrArg (ψ τ) (congrFun h2 i)
        rw [RingHom.map_mulVec, Matrix.map_mul] at this
        rw [Matrix.mulVec_mulVec]
        exact this.trans (map_mul (ψ τ) gt (vt i))
      refine ⟨fun τ => (∏ σ ∈ Finset.univ.erase τ, cF σ) • (YF τ *ᵥ v τ), mem_tot.2 fun τ i => ?_, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
        exact mul_mem (prod_mem fun σ _ => hcF σ)
          (sum_mem fun j _ => mul_mem (hYF τ i j) (mem_tot.1 hv τ j))
      · change F.app _ = _
        funext τ
        rw [Hom.app_apply, Matrix.mulVec_smul, hkey, smul_smul,
          Finset.prod_erase_mul _ _ (Finset.mem_univ τ)]
        rfl
    · rintro ⟨w, hw, rfl⟩
      have hlat : ∀ z, latW g (latW f z) = 0 := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul w x =>
          have h0 : ((g.f.restrictScalars O).restrict g.T_le) (((f.f.restrictScalars O).restrict f.T_le) x) = 0 :=
            Subtype.ext ((hS.2.2.2.1 (f.f x)).2 ⟨x, rfl⟩)
          simp only [latW, TensorProduct.map_tmul, LinearMap.id_apply, h0, TensorProduct.tmul_zero]
        | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]
      have hW : ∀ x, homW t ϖ H (homW t ϖ F x) = 0 := fun x =>
        I₂.j.injective (by rw [hH, hF, hlat, map_zero])
      have hM : (Ht * Ft).map φ = 0 := by
        ext i j
        have := congrFun (hW (Pi.single j 1)) i
        rw [homW_apply, homW_apply, Matrix.mulVec_mulVec] at this
        simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply] at this
        rw [Matrix.map_mul]
        exact this
      have hz : Ht * Ft = 0 := Matrix.map_injective hφ (hM.trans (Matrix.map_zero _ (map_zero φ)).symm)
      have hHF : ∀ τ, H.mat τ * F.mat τ = 0 := fun τ => by
        have := congrArg (fun M => M.map (ψ τ)) hz
        simp only [Matrix.map_mul, Matrix.map_zero _ (map_zero (ψ τ))] at this
        exact this
      change H.app (F.app w) = 0
      funext τ
      rw [Hom.app_apply, Hom.app_apply, Matrix.mulVec_mulVec, hHF τ, Matrix.zero_mulVec]
      rfl
  · exact (GlobalTheory.T.finiteLength_coker_of_surjective_mod_uniformizer O K l e a κ μ P₁ P₂ H).1 fun τ => ⟨YH τ, cH τ, hYH τ, hkH τ, hHY τ⟩

theorem isExactTriple_of_isSESLat : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (μ : Type) [Fintype μ] [DecidableEq μ] (P₀ : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (P₁ : PhiMod ↥(OL LL) ↥LL.1 l e a κ) (P₂ : PhiMod ↥(OL LL) ↥LL.1 l e a μ) (T₀ T₁ T₂ : QLat LL) (I₀ : Ident (thetaW a LL) ϖ P₀ T₀) (I₁ : Ident (thetaW a LL) ϖ P₁ T₁) (I₂ : Ident (thetaW a LL) ϖ P₂ T₂) (f : LatHom T₀.L T₁.L) (g : LatHom T₁.L T₂.L) (F : GlobalTheory.BK.Hom P₀ P₁) (G : GlobalTheory.BK.Hom P₁ P₂), IsSESLat (Qp := ℚ_[l]) f g → IsMapOf I₀ I₁ f F → IsMapOf I₁ I₂ g G → IsExactTriple F G := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ κ _ _ μ _ _ P₀ P₁ P₂ T₀ T₁ T₂ I₀ I₁ I₂ f g F G hS hF hG
  exact isExactTriple_of_isSESLat_gen (thetaW a LL) ϖ hS hF hG

end GlobalTheory.BKExact
end
end
end
