module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.InfGLScalar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.AdelicLiftHasModerateGrowth
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashUnnormalizedConstMul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.RationalGL2InfiniteFiniteFactor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertHolomorphicUnnormalizedSlashOfPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashEvalSmoothWeightLowering
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashRationalMatrixProperties
import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.MaximalCompactGL2FiniteAdeleCharacterization

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.AdelicLiftKFiniteOfIsLift

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.LiftCpt

open UpperHalfPlane hiding I

theorem rot_smul_I (x : GL (Fin 2) ℝ) (h1 : x.val 0 0 ^ 2 + x.val 0 1 ^ 2 = 1) (hc : x.val 1 0 = -x.val 0 1)
    (hd : x.val 1 1 = x.val 0 0) : x • UpperHalfPlane.I = UpperHalfPlane.I := by
  have hdet : x.val.det = 1 := by rw [Matrix.det_fin_two, hc, hd]; linear_combination h1
  have hp : 0 < x.val.det := by rw [hdet]; exact one_pos
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (by simpa using hp), div_eq_iff (denom_ne_zero _ _), num, denom, hc, hd, coe_I]
  push_cast
  linear_combination (x.val 0 1 : ℂ) * Complex.I_sq

theorem orth_cases {a b c d : ℝ} (h1 : a ^ 2 + b ^ 2 = 1) (h2 : c ^ 2 + d ^ 2 = 1)
    (h3 : a * c + b * d = 0) : (c = -b ∧ d = a) ∨ (c = b ∧ d = -a) := by
  have hD : (a * d - b * c - 1) * (a * d - b * c + 1) = 0 := by
    linear_combination (c ^ 2 + d ^ 2) * h1 + h2 - (a * c + b * d) * h3
  rcases mul_eq_zero.1 hD with h | h
  · exact Or.inl ⟨by linear_combination (-c) * h1 + a * h3 - b * h, by linear_combination (-d) * h1 + b * h3 + a * h⟩
  · exact Or.inr ⟨by linear_combination (-c) * h1 + a * h3 - b * h, by linear_combination (-d) * h1 + b * h3 + a * h⟩

variable {F : Type} [Field F] [NumberField F]

def sg (s : InfinitePlace F → Bool) : InfinitePlace F → ℝ := fun v => if s v then 1 else -1

omit [NumberField F] in
theorem sg_mul (s : InfinitePlace F → Bool) : sg s * sg s = 1 := by
  funext v
  simp only [sg, Pi.mul_apply, Pi.one_apply]
  split_ifs <;> norm_num

def epsG (s : InfinitePlace F → Bool) : GL (Fin 2) (InfinitePlace F → ℝ) where
  val := !![sg s, 0; 0, 1]
  inv := !![sg s, 0; 0, 1]
  val_inv := by simp [sg_mul, Matrix.one_fin_two]
  inv_val := by simp [sg_mul, Matrix.one_fin_two]

variable [IsTotallyReal F]

theorem rot_rt (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : TR.Sm F 2) (hφ : IsLift k Ψ φ.1)
    (x : GL (Fin 2) (InfinitePlace F → ℝ)) (h1 : ∀ v, x.val 0 0 v ^ 2 + x.val 0 1 v ^ 2 = 1)
    (hc : ∀ v, x.val 1 0 v = -x.val 0 1 v) (hd : ∀ v, x.val 1 1 v = x.val 0 0 v) :
    ∃ c : ℂ, TR.rt F 2 (TR.infGL F 2 x) φ = c • φ := by
  have hp : Pos x := fun v => by
    rw [Matrix.det_fin_two]
    simp only [Pi.sub_apply, Pi.mul_apply, hc v, hd v]
    nlinarith [h1 v]
  have ha : act x (fun _ => UpperHalfPlane.I) = fun _ => UpperHalfPlane.I :=
    funext fun v => rot_smul_I (cmp v x) (h1 v) (hc v) (hd v)
  refine ⟨sl k x (fun _ => 1) (fun _ => UpperHalfPlane.I), Subtype.ext (funext fun g => ?_)⟩
  have hF : ∀ f : Hn F → ℂ, sl k x f (fun _ => UpperHalfPlane.I) =
      sl k x (fun _ => 1) (fun _ => UpperHalfPlane.I) * f (fun _ => UpperHalfPlane.I) := fun f => by
    simp only [sl, sl0, ha]
    ring
  rw [← TR.infGL_mul_finGL g]
  generalize Matrix.GeneralLinearGroup.map (TR.pInf F) g = y
  generalize Matrix.GeneralLinearGroup.map (pFin F) g = u
  obtain ⟨τ, hτ⟩ := (GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin F 1).2 y
  have e : ∀ y : GL (Fin 2) (InfinitePlace F → ℝ), φ.1 (TR.infGL F 2 y * finGL F 2 u) =
      φ.1 (TR.infGL F 2 (toInf τ * y) * finGL F 2 (toFin τ * u)) := fun y => by
    rw [← hφ.1 τ, (GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin F τ).1, map_mul, map_mul, mul_assoc, mul_assoc, ← mul_assoc (finGL F 2 (toFin τ)),
      ← TR.infGL_comm, mul_assoc]
  obtain ⟨q1, -, -, q2, -⟩ := SlashCocycle.slash_cocycle F k (toInf τ * y) x (Ψ (toFin τ * u)) hτ hp
  rw [TR.rt_apply]
  change _ = _ * φ.1 _
  rw [mul_assoc, ← TR.infGL_comm, ← mul_assoc, ← map_mul, e, e y, ← mul_assoc, hφ.2 _ q1, hφ.2 _ hτ, q2, hF]

theorem lift_cpt_finite : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : TR.Sm F 2), IsLift k Ψ φ.1 → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun r => TR.cptRep F 2 r φ)) := by
  intro F _ _ _ k Ψ φ hφ
  classical
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun s => TR.rt F 2 (TR.infGL F 2 (epsG s)) φ)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  refine Submodule.finiteDimensional_of_le
    (S₂ := Submodule.span ℂ (Set.range fun s => TR.rt F 2 (TR.infGL F 2 (epsG s)) φ)) (Submodule.span_le.2 ?_)
  rintro _ ⟨r, rfl⟩
  set x : GL (Fin 2) (InfinitePlace F → ℝ) := Unitary.toUnits r with hx
  have e : TR.cptRep F 2 r φ = TR.rt F 2 (TR.infGL F 2 x) φ := rfl
  have hr : ∀ v i j, x.val i 0 v * x.val j 0 v + x.val i 1 v * x.val j 1 v = if i = j then 1 else 0 := by
    intro v i j
    have h := congrArg (fun m => m i j v) r.2.2
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply, Pi.add_apply, Pi.mul_apply,
      star_trivial] at h
    rw [ite_apply] at h
    exact h
  have h1 : ∀ v, x.val 0 0 v ^ 2 + x.val 0 1 v ^ 2 = 1 := fun v => by
    have := hr v 0 0; simp only [if_true] at this; linear_combination this
  have h2 : ∀ v, x.val 1 0 v ^ 2 + x.val 1 1 v ^ 2 = 1 := fun v => by
    have := hr v 1 1; simp only [if_true] at this; linear_combination this
  have h3 : ∀ v, x.val 0 0 v * x.val 1 0 v + x.val 0 1 v * x.val 1 1 v = 0 := fun v => by simpa using hr v 0 1
  change TR.cptRep F 2 r φ ∈ _
  rw [e]
  clear_value x
  let s : InfinitePlace F → Bool := fun v => decide (x.val 1 0 v = -x.val 0 1 v ∧ x.val 1 1 v = x.val 0 0 v)
  have hv : (epsG s * x).val = !![sg s * x.val 0 0, sg s * x.val 0 1; x.val 1 0, x.val 1 1] := by
    ext i j : 2
    fin_cases i <;> fin_cases j <;> simp [epsG, Matrix.mul_apply, Fin.sum_univ_two]
  have hs : ∀ v, x.val 1 0 v = -(sg s v * x.val 0 1 v) ∧ x.val 1 1 v = sg s v * x.val 0 0 v := fun v => by
    by_cases h : x.val 1 0 v = -x.val 0 1 v ∧ x.val 1 1 v = x.val 0 0 v
    · have : sg s v = 1 := by simp only [sg, s, decide_eq_true_eq]; exact if_pos h
      rw [this, one_mul, one_mul]
      exact h
    · have : sg s v = -1 := by simp only [sg, s, decide_eq_true_eq]; exact if_neg h
      rw [this]
      have := (orth_cases (h1 v) (h2 v) (h3 v)).resolve_left h
      exact ⟨by linear_combination this.1, by linear_combination this.2⟩
  obtain ⟨c, hc⟩ := rot_rt k Ψ φ hφ (epsG s * x)
    (fun v => by
      have q : sg s v * sg s v = 1 := congrFun (sg_mul s) v
      rw [hv]
      change (sg s v * x.val 0 0 v) ^ 2 + (sg s v * x.val 0 1 v) ^ 2 = 1
      linear_combination (x.val 0 0 v ^ 2 + x.val 0 1 v ^ 2) * q + h1 v)
    (fun v => by rw [hv]; exact (hs v).1) (fun v => by rw [hv]; exact (hs v).2)
  have e2 : x = epsG s * (epsG s * x) := by
    rw [← mul_assoc, show epsG s * epsG s = 1 from Units.ext (epsG s).val_inv, one_mul]
  rw [e2, map_mul, map_mul, Module.End.mul_apply, hc, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)

end GlobalTheory.HilbertThetaSeries.LiftCpt

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.adelic_lift_kFinite_of_isLift : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : TR.Sm F 2), IsLift k Ψ φ.1 → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun r => TR.cptRep F 2 r φ)) := by
  first | exact @GlobalTheory.HilbertThetaSeries.LiftCpt.lift_cpt_finite | exact GlobalTheory.HilbertThetaSeries.LiftCpt.lift_cpt_finite | (intros; apply GlobalTheory.HilbertThetaSeries.LiftCpt.lift_cpt_finite <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.AdelicLiftMemSmoothKilledByLowering

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.LiftSmooth

open Matrix

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def PSet (F : Type) [Field F] : Set (TR.Lie F 2) := {x | ∀ v, 0 < (Matrix.of x).det v}

theorem isOpen_PSet : IsOpen (PSet F) := by
  have : PSet F = ⋂ v : InfinitePlace F, (fun x : TR.Lie F 2 => (Matrix.of x).det v) ⁻¹' Set.Ioi 0 := by
    ext x; simp [PSet]
  rw [this]
  exact isOpen_iInter_of_finite fun v =>
    isOpen_Ioi.preimage ((continuous_apply v).comp TR.contDiff_det.continuous)

theorem isUnit_of_mem_PSet {x : TR.Lie F 2} (hx : x ∈ PSet F) : IsUnit (Matrix.of x) :=
  (Matrix.isUnit_iff_isUnit_det _).2 (Pi.isUnit_iff.2 fun v => (hx v).ne'.isUnit)

theorem pos_one : Pos (1 : GL (Fin 2) (InfinitePlace F → ℝ)) := fun v => by simp

theorem key (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : GA F 2 → ℂ) (hΨ : ∀ g, Hol (Ψ g))
    (hL : IsLift k Ψ φ) (g : GA F 2) :
    ∃ f : Hn F → ℂ, Hol f ∧ f (fun _ => UpperHalfPlane.I) = φ g ∧
      ∀ u : GL (Fin 2) (InfinitePlace F → ℝ), Pos u →
        φ (g * TR.infGL F 2 u) = sl k u f fun _ => UpperHalfPlane.I := by
  set gi := Matrix.GeneralLinearGroup.map (TR.pInf F) g
  set gf := Matrix.GeneralLinearGroup.map (pFin F) g
  obtain ⟨τ, hτ⟩ := (GlobalTheory.T.rational_GL2_infinite_finite_factor F 1).2 gi
  have hdec := (GlobalTheory.T.rational_GL2_infinite_finite_factor F τ).1
  set M := toInf τ * gi
  set f := sl k M (Ψ (toFin τ * gf))
  have hf : Hol f := ((GlobalTheory.HilbertThetaSeries.HolKeep.main F k (Ψ (toFin τ * gf)) (Ψ (toFin τ * gf)) 1 (hΨ _) (hΨ _)).2.2.2.2.2 M hτ).2
  have hmain : ∀ u : GL (Fin 2) (InfinitePlace F → ℝ), Pos u →
      φ (g * TR.infGL F 2 u) = sl k u f fun _ => UpperHalfPlane.I := by
    intro u hu
    have hc := GlobalTheory.HilbertThetaSeries.SlashCocycle.slash_cocycle F k M u (Ψ (toFin τ * gf)) hτ hu
    have e : ratGL F 2 τ * (g * TR.infGL F 2 u) = TR.infGL F 2 (M * u) * finGL F 2 (toFin τ * gf) := by
      rw [hdec]
      refine TR.ga_ext ?_ ?_ <;> simp [map_mul, gi, gf, M, mul_assoc]
    rw [← hL.1 τ, e, hL.2 _ hc.1, hc.2.2.2.1]
  refine ⟨f, hf, ?_, hmain⟩
  have h1 := hmain 1 pos_one
  rw [map_one, mul_one] at h1
  rw [h1, (GlobalTheory.HilbertThetaSeries.SlashCocycle.slash_cocycle F k 1 1 f pos_one pos_one).2.2.2.2.2]

theorem chart_eq (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : GA F 2 → ℂ) (hΨ : ∀ g, Hol (Ψ g))
    (hL : IsLift k Ψ φ) (g : GA F 2) (f : Hn F → ℂ)
    (hfe : ∀ u : GL (Fin 2) (InfinitePlace F → ℝ), Pos u →
        φ (g * TR.infGL F 2 u) = sl k u f fun _ => UpperHalfPlane.I)
    (A : (Fin 2 → Fin 2 → InfinitePlace F → ℝ) → ℂ)
    (hA : ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), Pos h → A (Matrix.of.symm h.val) = sl k h f fun _ => UpperHalfPlane.I)
    {y : TR.Lie F 2} (hy : y ∈ PSet F) : TR.chart φ g y = A y := by
  obtain ⟨w, hw⟩ := isUnit_of_mem_PSet hy
  have e : y = TR.toL w.val := hw.symm
  subst e
  have hpw : Pos w := hy
  rw [TR.chart_val, hfe w hpw, hA w hpw]

end GlobalTheory.HilbertThetaSeries.LiftSmooth

open GlobalTheory.HilbertThetaSeries.LiftSmooth in
theorem GlobalTheory.HilbertThetaSeries.lift_smooth_lowering : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : GA F 2 → ℂ), (∀ g, Hol (Ψ g)) → IsLift k Ψ φ → ∃ h : φ ∈ TR.Sm F 2, ∀ v, TR.Eop v 0 1 ⟨φ, h⟩ - TR.Eop v 1 0 ⟨φ, h⟩ = (Complex.I * k) • (⟨φ, h⟩ : TR.Sm F 2) ∧ TR.Eop v 0 0 ⟨φ, h⟩ - TR.Eop v 1 1 ⟨φ, h⟩ = Complex.I • (TR.Eop v 0 1 ⟨φ, h⟩ + TR.Eop v 1 0 ⟨φ, h⟩) := by
  intro F _ _ _ k Ψ φ hΨ hL
  classical
  have hsm : φ ∈ TR.Sm F 2 := by
    intro g
    apply contDiffOn_of_locally_contDiffOn
    intro x hx
    obtain ⟨u, hu⟩ := id hx
    have ex : x = TR.toL u.val := hu.symm
    obtain ⟨f, hf, -, hfe⟩ := key k Ψ φ hΨ hL (g * TR.infGL F 2 u)
    obtain ⟨A, hA1, hA2, -⟩ := GlobalTheory.T.hilbert_slash_eval_smooth_weight_lowering F k f hf
    set L := TR.lmul (TR.toL (u⁻¹).val)
    refine ⟨L ⁻¹' PSet F, isOpen_PSet.preimage L.continuous, ?_, ?_⟩
    · show ∀ v, 0 < (Matrix.of (L x)).det v
      intro v
      have : Matrix.of (L x) = 1 := by
        subst ex
        show ((u⁻¹ : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix _ _ _) * u.val = 1
        simp
      rw [this]; simp
    · refine (hA2.comp_inter L.contDiff.contDiffOn).congr ?_
      intro y hy
      have hy1 : IsUnit (Matrix.of y) := hy.1
      obtain ⟨w, hw⟩ := hy1
      have ey : y = TR.toL w.val := hw.symm
      have hLy : L y = TR.toL (u⁻¹ * w).val := by subst ey; rfl
      have hpos : Pos (u⁻¹ * w) := by
        intro v; have := hy.2 v; rw [hLy] at this; exact this
      simp only [Function.comp_apply]
      rw [hLy, hA1 _ hpos, ← hfe _ hpos, ey, TR.chart_val, mul_assoc, ← map_mul, mul_inv_cancel_left]
  refine ⟨hsm, fun v => ?_⟩
  have hD : ∀ g, ∃ A : (Fin 2 → Fin 2 → InfinitePlace F → ℝ) → ℂ,
      TR.chart φ g =ᶠ[nhds (TR.oneL F 2)] A ∧
      fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single 0 1 (Pi.single v 1))) -
          fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single 1 0 (Pi.single v 1))) =
        Complex.I * k * φ g ∧
      fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single 0 0 (Pi.single v 1))) -
          fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single 1 1 (Pi.single v 1))) =
        Complex.I * (fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single 0 1 (Pi.single v 1))) +
          fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single 1 0 (Pi.single v 1)))) := by
    intro g
    obtain ⟨f, hf, hfg, hfe⟩ := key k Ψ φ hΨ hL g
    obtain ⟨A, hA1, -, hA3⟩ := GlobalTheory.T.hilbert_slash_eval_smooth_weight_lowering F k f hf
    obtain ⟨h1, h2⟩ := hA3 v _ fun _ _ => rfl
    refine ⟨A, ?_, ?_, h2⟩
    · have hmem : TR.oneL F 2 ∈ PSet F := fun w => by simp
      exact Filter.eventually_of_mem (isOpen_PSet.mem_nhds hmem) fun y hy => chart_eq k Ψ φ hΨ hL g f hfe A hA1 hy
    · rw [h1, hfg]
  constructor
  · refine Subtype.ext (funext fun g => ?_)
    obtain ⟨A, hA, h1, -⟩ := hD g
    show TR.lieD _ φ g - TR.lieD _ φ g = (Complex.I * k) * φ g
    rw [TR.lieD, TR.lieD, hA.fderiv_eq, h1]
  · refine Subtype.ext (funext fun g => ?_)
    obtain ⟨A, hA, -, h2⟩ := hD g
    show TR.lieD _ φ g - TR.lieD _ φ g = Complex.I * (TR.lieD _ φ g + TR.lieD _ φ g)
    rw [TR.lieD, TR.lieD, TR.lieD, TR.lieD, hA.fderiv_eq, h2]

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.adelic_lift_mem_smooth_killed_by_lowering : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : GA F 2 → ℂ), (∀ g, Hol (Ψ g)) → IsLift k Ψ φ → ∃ h : φ ∈ TR.Sm F 2, ∀ v, TR.Eop v 0 1 ⟨φ, h⟩ - TR.Eop v 1 0 ⟨φ, h⟩ = (Complex.I * k) • (⟨φ, h⟩ : TR.Sm F 2) ∧ TR.Eop v 0 0 ⟨φ, h⟩ - TR.Eop v 1 1 ⟨φ, h⟩ = Complex.I • (TR.Eop v 0 1 ⟨φ, h⟩ + TR.Eop v 1 0 ⟨φ, h⟩) := by
  first | exact @GlobalTheory.HilbertThetaSeries.lift_smooth_lowering | exact GlobalTheory.HilbertThetaSeries.lift_smooth_lowering | (intros; apply GlobalTheory.HilbertThetaSeries.lift_smooth_lowering <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsAdelicLiftOfHilbertSystem

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.AdelicLift

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem sl_indep {k : ℕ} {Ψ : GL (Fin 2) (Af F) → Hn F → ℂ} (hΨ : Sys k Ψ) (h : GL (Fin 2) (InfinitePlace F → ℝ))
    (g : GL (Fin 2) (Af F)) (τ τ' : GL (Fin 2) F) (hτ : Pos (toInf τ * h)) (hτ' : Pos (toInf τ' * h)) :
    sl k (toInf τ * h) (Ψ (toFin τ * g)) = sl k (toInf τ' * h) (Ψ (toFin τ' * g)) := by
  have hinv : Pos (toInf τ' * h)⁻¹ := (SlashCocycle.slash_cocycle F k _ _ 0 hτ' hτ').2.1
  have hγ : Pos (toInf (τ * τ'⁻¹)) := by
    have e : toInf (τ * τ'⁻¹) = (toInf τ * h) * (toInf τ' * h)⁻¹ := by
      rw [map_mul, map_inv]; group
    rw [e]
    exact (SlashCocycle.slash_cocycle F k _ _ 0 hτ hinv).1
  have hTP : TP (τ * τ'⁻¹).val.det := ((GlobalTheory.T.hilbert_slash_rational_matrix_properties F k 0).2.1 _).1.1 hγ
  have e1 : toInf τ * h = toInf (τ * τ'⁻¹) * (toInf τ' * h) := by
    rw [map_mul, map_inv]; group
  have e2 : toFin τ * g = toFin (τ * τ'⁻¹) * (toFin τ' * g) := by
    rw [map_mul, map_inv]; group
  rw [e1, e2, (SlashCocycle.slash_cocycle F k _ _ _ hγ hτ').2.2.2.1, hΨ.left _ hTP]

theorem map_scalar {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (z : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map f.toMonoidHom z) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Matrix.GeneralLinearGroup.scalar]
  · simp [Matrix.GeneralLinearGroup.scalar, hij]

theorem scalar_comm {R : Type} [CommRing R] (z : Rˣ) (g : GL (Fin 2) R) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g := by
  apply Units.ext
  exact ((Matrix.scalar_commute (z : R) (fun r => Commute.all _ r) g.val).eq).symm

theorem exists_lift : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), Even k → ∀ (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ), Sys k Ψ → ∃ φ : GA F 2 → ℂ, IsLift k Ψ φ ∧ (∀ u ∈ KLev F 2 1, ∀ g, φ (g * finGL F 2 u) = φ g) ∧ ∀ (z : Ideles F) (g : GA F 2), φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = φ g := by
  intro F _ _ _ k hk Ψ hΨ
  choose τ hτ using (GlobalTheory.T.rational_GL2_infinite_finite_factor F 1).2
  let G : GL (Fin 2) (InfinitePlace F → ℝ) → GL (Fin 2) (Af F) → Hn F → ℂ :=
    fun h g => sl k (toInf (τ h) * h) (Ψ (toFin (τ h) * g))
  have hG : ∀ h g σ, Pos (toInf σ * h) → G h g = sl k (toInf σ * h) (Ψ (toFin σ * g)) :=
    fun h g σ hσ => sl_indep hΨ h g _ _ (hτ h) hσ
  refine ⟨fun x => G (Matrix.GeneralLinearGroup.map (TR.pInf F) x) (Matrix.GeneralLinearGroup.map (pFin F) x)
    fun _ => UpperHalfPlane.I, ⟨fun γ x => ?_, fun h hh g => ?_⟩, fun u hu x => ?_, fun z x => ?_⟩
  · rw [(GlobalTheory.T.rational_GL2_infinite_finite_factor F γ).1]
    simp only [map_mul, TR.pInf_infGL, TR.pInf_finGL, TR.pFin_infGL, pFin_finGL, mul_one, one_mul]
    generalize Matrix.GeneralLinearGroup.map (TR.pInf F) x = h
    generalize Matrix.GeneralLinearGroup.map (pFin F) x = g
    have hp : Pos (toInf (τ (toInf γ * h) * γ) * h) := by
      rw [map_mul, mul_assoc]; exact hτ _
    rw [hG h g _ hp]
    simp only [G, map_mul, mul_assoc]
  · simp only [map_mul, TR.pInf_infGL, TR.pInf_finGL, TR.pFin_infGL, pFin_finGL, mul_one, one_mul]
    rw [hG h g 1 (by simpa using hh)]
    simp only [map_one, one_mul]
  · simp only [map_mul, TR.pInf_finGL, pFin_finGL, mul_one, G]
    rw [← mul_assoc, hΨ.right _ u hu]
  · simp only [map_mul, map_scalar]
    generalize Matrix.GeneralLinearGroup.map (TR.pInf F) x = h
    generalize Matrix.GeneralLinearGroup.map (pFin F) x = g
    generalize Units.map (TR.pInf F).toMonoidHom z = t
    generalize Units.map (pFin F).toMonoidHom z = s
    have e : toInf (τ h) * (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) t * (toInf (τ h) * h) := by
      rw [← mul_assoc, scalar_comm, mul_assoc]
    have e' : toFin (τ h) * (Matrix.GeneralLinearGroup.scalar (Fin 2) s * g) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) s * (toFin (τ h) * g) := by
      rw [← mul_assoc, scalar_comm, mul_assoc]
    have H := (GlobalTheory.T.hilbert_slash_rational_matrix_properties F k (Ψ (toFin (τ h) * g))).2.2.1 hk t _ (hτ h)
    rw [hG _ _ (τ h) (by rw [e]; exact H.1), e, e', hΨ.cent, H.2]

end GlobalTheory.HilbertThetaSeries.AdelicLift

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_adelic_lift_of_hilbert_system : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), Even k → ∀ (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ), Sys k Ψ → ∃ φ : GA F 2 → ℂ, IsLift k Ψ φ ∧ (∀ u ∈ KLev F 2 1, ∀ g, φ (g * finGL F 2 u) = φ g) ∧ ∀ (z : Ideles F) (g : GA F 2), φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = φ g := by
  first | exact @GlobalTheory.HilbertThetaSeries.AdelicLift.exists_lift | exact GlobalTheory.HilbertThetaSeries.AdelicLift.exists_lift | (intros; apply GlobalTheory.HilbertThetaSeries.AdelicLift.exists_lift <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsIsHolAdelicLiftOfEvenWeightSystem

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem lift_isHol : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), Even k →
    ∀ (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ), Sys k Ψ → ∃ φ : TR.Sm F 2, IsLift k Ψ φ.1 ∧ IsHol k (fun _ => 0) 1 φ := by
  intro F _ _ _ k hk Ψ hΨ
  obtain ⟨φ₀, hL, hR, hZ⟩ := GlobalTheory.T.exists_adelic_lift_of_hilbert_system F k hk Ψ hΨ
  obtain ⟨hsm, hlie⟩ := GlobalTheory.T.adelic_lift_mem_smooth_killed_by_lowering F k Ψ φ₀ hΨ.hol hL
  let φ : TR.Sm F 2 := ⟨φ₀, hsm⟩
  have hfix : ∀ u ∈ KLev F 2 1, TR.finRep F 2 u φ = φ := fun u hu =>
    Subtype.ext (funext fun g => hR u hu g)
  have hlev : IsOpen {u | TR.finRep F 2 u φ = φ} := by
    let H : Subgroup (GL (Fin 2) (Af F)) :=
      { carrier := {u | TR.finRep F 2 u φ = φ}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, Module.End.mul_apply, hb, ha]
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq] at ha ⊢
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    exact Subgroup.isOpen_mono (H₁ := KLev F 2 1) (H₂ := H) hfix (isOpen_KLev (F := F) (n := 2) (M := 1) le_rfl)
  have hcen : ∀ (z : Ideles F) (g : GA F 2),
      φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = (((1 : HChar F).1 z : ℂˣ) : ℂ) * φ.1 g := by
    intro z g
    simp only [OneMemClass.coe_one, MonoidHom.one_apply, Units.val_one, one_mul]
    exact hZ z g
  have haut : TR.IsAutForm φ :=
    ⟨hL.1, hlev, GlobalTheory.T.adelic_lift_kFinite_of_isLift F k Ψ φ hL,
      UpperTheory.V.Af.Nf.zFin F k 1 IsOfFinOrder.one φ hcen (fun v => (hlie v).1) (fun v => (hlie v).2),
      GlobalTheory.T.adelic_lift_has_moderate_growth F k Ψ φ₀ hΨ.gr hL⟩
  refine ⟨φ, hL, haut, fun w u hu => hfix _ ((GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F).2.2.1 w u hu), hcen, fun v => (hlie v).1,
    fun v => (hlie v).2⟩

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_isHol_adelic_lift_of_even_weight_system : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), Even k → ∀ (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ), Sys k Ψ → ∃ φ : TR.Sm F 2, IsLift k Ψ φ.1 ∧ IsHol k (fun _ => 0) 1 φ := by
  first | exact @GlobalTheory.HilbertThetaSeries.lift_isHol | exact GlobalTheory.HilbertThetaSeries.lift_isHol | (intros; apply GlobalTheory.HilbertThetaSeries.lift_isHol <;> assumption)
end
end
