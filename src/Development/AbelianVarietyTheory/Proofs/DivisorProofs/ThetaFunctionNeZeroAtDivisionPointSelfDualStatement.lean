module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CardLePowOfLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ClassicalThetaLevelAndLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EntirePeriodicEqZeroOfFourierCoeffEqZero
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsApplySubSmulNeZeroAndApplyAddNeZero
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.FourierCoeffUnitCubeTranslateOfEntirePeriodic
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanThetaOfLevel
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.RiemannThetaLevelOneNeZero
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ThetaQuasiPeriods.Transl
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
public import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.FieldTheory.IsAlgClosed.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDivisionPointNeZero

section

@[expose] public section

open ReciprocityTheory.PTheta Complex Matrix

namespace GlobalTheory.ThetaDivisionPoints

theorem theta_add_int_div {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm) {N : ℕ}
    (hN : (N : ℂ) ≠ 0) (a : Fin g → ℝ) (z : Fin g → ℂ) (m : Fin g → ℤ) :
    theta a 0 ((N : ℂ) • (z + (N : ℂ)⁻¹ • ofIntVec m)) ((N : ℂ) • τ) =
      eC (ofRealVec a ⬝ᵥ ofIntVec m) * theta a 0 ((N : ℂ) • z) ((N : ℂ) • τ) := by
  have h := thetaQuasiPeriod_holds (Fin g) a 0 ((N : ℂ) • z) ((N : ℂ) • τ) 0 m (hτ.smul _)
  rw [ofIntVec_zero, mulVec_zero, add_zero] at h
  rw [smul_add, smul_smul, mul_inv_cancel₀ hN, one_smul, h]
  congr 1
  simp [autFactor, ofIntVec_zero, eC_zero]

theorem theta_add_tau_div {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm) {N : ℕ}
    (hN : (N : ℂ) ≠ 0) (a : Fin g → ℝ) (z : Fin g → ℂ) (n : Fin g → ℤ) :
    ∃ u : ℂ, u ≠ 0 ∧ theta a 0 ((N : ℂ) • (z + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n)) ((N : ℂ) • τ) =
      u * theta (a + fun i => (n i : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) := by
  have h := thetaRealTransl_holds (Fin g) a 0 (fun i => (n i : ℝ) / N) 0 ((N : ℂ) • z)
    ((N : ℂ) • τ) (hτ.smul _)
  have e0 : ofRealVec (0 : Fin g → ℝ) = 0 := by ext i; simp [ofRealVec]
  have e1 : ofRealVec (fun i => (n i : ℝ) / N) = (N : ℂ)⁻¹ • ofIntVec n := by
    ext i; simp [ofRealVec, ofIntVec, div_eq_inv_mul]
  have e2 : ((N : ℂ) • τ) *ᵥ ((N : ℂ)⁻¹ • ofIntVec n) = (N : ℂ) • (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n := by
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul]
  rw [e0, add_zero, add_zero (0 : Fin g → ℝ)] at h
  rw [smul_add, ← e2, ← e1]
  exact ⟨_, Complex.exp_ne_zero _, h⟩

noncomputable def intChar {g : ℕ} (N : ℕ) (c : Fin g → Fin N) : Multiplicative (Fin g → ℤ) →* ℂ where
  toFun m := eC (ofRealVec (fun i => ((c i : ℕ) : ℝ) / N) ⬝ᵥ ofIntVec m.toAdd)
  map_one' := by simp [ofIntVec_zero, eC_zero]
  map_mul' m m' := by rw [toAdd_mul, ofIntVec_add, dotProduct_add, eC_add]

theorem intChar_injective {g : ℕ} {N : ℕ} (hN : N ≠ 0) :
    Function.Injective (intChar (g := g) N) := by
  intro c c' h
  funext i
  have key : ∀ d : Fin g → Fin N, intChar N d (Multiplicative.ofAdd (Pi.single i 1)) =
      cexp (2 * Real.pi * I / N) ^ (d i : ℕ) := by
    intro d
    change eC (ofRealVec (fun i => ((d i : ℕ) : ℝ) / N) ⬝ᵥ ofIntVec (Pi.single i 1)) = _
    rw [GlobalTheory.ThetaSpan.ofIntVec_single, dotProduct_single_one, ← Complex.exp_nat_mul, eC]
    congr 1
    simp only [ofRealVec]
    push_cast
    ring
  have h1 := key c
  rw [h, key c'] at h1
  exact Fin.ext ((Complex.isPrimitiveRoot_exp N hN).pow_inj (c i).2 (c' i).2 h1.symm)

theorem mem_span_of_laws {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) {N : ℕ}
    (hN : 1 ≤ N) {f : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f ∧
      (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) ∧
      ∀ (j : Fin g) z, f (z + τ.mulVec (Pi.single j 1)) =
        eC (-(τ j j) / 2) ^ N * cexp (-(2 * Real.pi * I) * N * z j) * f z) :
    f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z : Fin g → ℂ) =>
      theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) := by
  have f4 := @GlobalTheory.fourierCoeff_unitCube_translate_of_entire_periodic
  have f5 := @GlobalTheory.entire_periodic_eq_zero_of_fourierCoeff_eq_zero f4
  have hdim := @GlobalTheory.ClassicalTheta.card_le_pow_of_linearIndependent f4 f5
  obtain ⟨hlev, hli⟩ := classicalTheta_level_and_linearIndependent' g τ hτ N hN
  by_contra hnot
  have hopt := hli.option hnot
  have hcard : Fintype.card (Option (Fin g → Fin N)) = N ^ g + 1 := by simp
  let e := (Fintype.equivFinOfCardEq hcard).symm
  have hli' := hopt.comp e e.injective
  have := hdim g N τ (fun j => eC (-(τ j j) / 2)) hN (fun j => Complex.exp_ne_zero _)
    (N ^ g + 1) _ (fun k => ?_) hli'
  · omega
  · simp only [Function.comp_apply]
    rcases e k with _ | c
    · exact hf
    · exact ⟨(hlev c).1, GlobalTheory.ThetaSpan.laws_of_level τ N _ (hlev c).2⟩

theorem exists_theta_ne_zero {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g))
    {N : ℕ} (hN : 2 ≤ N) (z : Fin g → ℂ) : ∃ c : Fin g → Fin N,
      theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0 := by
  have f8 := @GlobalTheory.riemannTheta_level_one_ne_zero classicalTheta_level_and_linearIndependent'
  obtain ⟨f, hf, hz⟩ := GlobalTheory.exists_level_apply_ne_zero_of_two_le f8 g τ hτ N hN z
  have hs := mem_span_of_laws hτ (by omega : 1 ≤ N) ⟨hf.1, GlobalTheory.ThetaSpan.laws_of_level τ N f hf.2⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hs
  by_contra hcon
  push Not at hcon
  apply hz
  rw [← ha]
  simp [Finset.sum_apply, hcon]

theorem exists_division_point_ne_zero :
    ∀ (g N : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (β : Fin g → ℂ) (f : (Fin g → ℂ) → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → 2 ≤ N → (∀ j, β j ≠ 0) → Differentiable ℂ f → f ≠ 0 → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → (∀ (j : Fin g) z, f (z + τ.mulVec (Pi.single j 1)) = β j * cexp (-(2 * Real.pi * I) * N * z j) * f z) → ∃ m n : Fin g → ℤ, f ((N : ℂ)⁻¹ • ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) ≠ 0 := by
  intro g N τ β f hs hp hN hβ hd hf0 hper hlaw
  have hτ : τ ∈ SiegelH (Fin g) := ⟨hs, hp⟩
  have hN0 : N ≠ 0 := by omega
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  have hπ : (2 * Real.pi * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let w : Fin g → ℂ := fun j => Complex.log (β j) / (2 * Real.pi * I * N) + τ j j / 2
  have hw : ∀ j, β j * cexp (-(2 * Real.pi * I) * N * w j) = eC (-(τ j j) / 2) ^ N := by
    intro j
    rw [eC, ← Complex.exp_nat_mul]
    conv_lhs => rw [← Complex.exp_log (hβ j), ← Complex.exp_add]
    congr 1
    simp only [w]
    field_simp
    ring
  have hF := mem_span_of_laws (f := fun z => f (z + w)) hτ (by omega : 1 ≤ N)
    ⟨hd.comp (by fun_prop), fun i z => by
      rw [add_right_comm, hper], fun j z => by
      rw [add_right_comm, hlaw, ← hw j, Pi.add_apply, mul_add, Complex.exp_add]
      ring⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hF
  obtain ⟨c₀, hc₀⟩ : ∃ c, a c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hf0
    funext z
    have := congrFun ha (z - w)
    simpa [hcon] using this.symm
  by_contra hcon
  push Not at hcon
  have hvan : ∀ n : Fin g → ℤ, theta (fun i => ((c₀ i : ℕ) : ℝ) / N) 0
      ((N : ℂ) • (-w + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n)) ((N : ℂ) • τ) = 0 := by
    intro n
    have hli := (linearIndependent_monoidHom (Multiplicative (Fin g → ℤ)) ℂ).comp _
      (intChar_injective (g := g) hN0)
    have := Fintype.linearIndependent_iff.1 hli
      (fun c => a c * theta (fun i => ((c i : ℕ) : ℝ) / N) 0
        ((N : ℂ) • (-w + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n)) ((N : ℂ) • τ)) (by
        funext m
        have h1 := congrFun ha (-w + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n + (N : ℂ)⁻¹ • ofIntVec m.toAdd)
        have h2 := hcon m.toAdd n
        have e : -w + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n + (N : ℂ)⁻¹ • ofIntVec m.toAdd + w =
            (N : ℂ)⁻¹ • ((fun i => (m.toAdd i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) := by
          rw [smul_add]
          change _ = (N : ℂ)⁻¹ • ofIntVec m.toAdd + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n
          abel
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
        rw [e, h2] at h1
        rw [Pi.zero_apply, ← h1]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [theta_add_int_div hs hNC, mul_assoc, mul_comm (eC _)]
        rfl) c₀
    exact (mul_eq_zero.1 this).resolve_left hc₀
  obtain ⟨c, hc⟩ := exists_theta_ne_zero hτ hN (-w)
  obtain ⟨u, hu, h⟩ := theta_add_tau_div hs hNC (fun i => ((c₀ i : ℕ) : ℝ) / N) (-w)
    (fun i => ((c i : ℕ) : ℤ) - ((c₀ i : ℕ) : ℤ))
  rw [hvan] at h
  have e : ((fun i => ((c₀ i : ℕ) : ℝ) / N) +
      fun i => ((((c i : ℕ) : ℤ) - ((c₀ i : ℕ) : ℤ) : ℤ) : ℝ) / N) =
      fun i => ((c i : ℕ) : ℝ) / N := by
    funext i
    simp only [Pi.add_apply]
    push_cast
    ring
  rw [e] at h
  exact mul_ne_zero hu hc h.symm

end GlobalTheory.ThetaDivisionPoints
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDivisionPointNeZeroStatement

section

@[expose] public section

open Complex Matrix

theorem _root_.GlobalTheory.T.exists_theta_division_point_ne_zero : ∀ (g N : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (β : Fin g → ℂ) (f : (Fin g → ℂ) → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → 2 ≤ N → (∀ j, β j ≠ 0) → Differentiable ℂ f → f ≠ 0 → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → (∀ (j : Fin g) z, f (z + τ.mulVec (Pi.single j 1)) = β j * cexp (-(2 * Real.pi * I) * N * z j) * f z) → ∃ m n : Fin g → ℤ, f ((N : ℂ)⁻¹ • ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) ≠ 0 := by
  first | exact @GlobalTheory.ThetaDivisionPoints.exists_division_point_ne_zero | exact GlobalTheory.ThetaDivisionPoints.exists_division_point_ne_zero | (intros; apply GlobalTheory.ThetaDivisionPoints.exists_division_point_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionNeZeroAtDivisionPointSelfDual

section

@[expose] public section

open Complex Matrix

namespace GlobalTheory.ThetaDivisionPoints

theorem eq_zero_of_im_eq_zero {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) {S : Set (Fin g → ℂ)}
    (hS : Submodule.span ℝ S = ⊤) {z : Fin g → ℂ}
    (hz : ∀ m ∈ S, (z ⬝ᵥ Hm.mulVec (star m)).im = 0) : z = 0 := by
  have h : ∀ m, (z ⬝ᵥ Hm.mulVec (star m)).im = 0 := by
    intro m
    have hm : m ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem m hm => exact hz m hm
    | zero => simp
    | add a b _ _ ha hb => rw [star_add, mulVec_add, dotProduct_add, add_im, ha, hb, add_zero]
    | smul t a _ ha =>
      rw [star_smul, mulVec_smul, dotProduct_smul, smul_im, ha, smul_zero]
  by_contra hne
  have h1 := hpos z hne
  have h2 := h (I • z)
  rw [star_smul, mulVec_smul, dotProduct_smul] at h2
  simp at h2
  linarith

theorem exists_ne_zero_of_principal {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (hd : DiscreteTopology Λ) (hs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ)
    (hH : Hm.IsHermitian) (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (hχ : ∀ l, ‖χ l‖ = 1)
    (hE : ∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)
    (hbij : Function.Bijective Ef) (n : ℕ) (hn : 2 ≤ n) (f : (Fin g → ℂ) → ℂ)
    (hdf : Differentiable ℂ f) (h0 : f ≠ 0)
    (hf : ∀ (l : Λ) z, f (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
      Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) ^ n * f z) :
    ∃ l ∈ Λ, f ((n : ℂ)⁻¹ • l) ≠ 0 := by
  obtain ⟨φ, τ, Q, b, hτ, hτp, hΛ, hQ, -, hb, h1, h2⟩ :=
    GlobalTheory.SiegelNormalForm.exists_normal_form g Λ hd hs Hm χ Ef hH hpos hχ hE hbij
  have hφ : Differentiable ℂ (fun z => φ z) :=
    (LinearMap.toContinuousLinearMap φ.toLinearMap).differentiable
  have key := GlobalTheory.T.exists_theta_division_point_ne_zero g n τ (fun j => b j ^ n) (fun z => f (φ z) * cexp (-(n * Q z))) hτ hτp hn
    (fun j => pow_ne_zero _ (hb j)) ((hdf.comp hφ).mul ((hQ.const_mul (n : ℂ)).neg.cexp)) ?_ ?_ ?_
  · obtain ⟨m, k, h⟩ := key
    refine ⟨φ _, (hΛ _).2 ⟨m, k, rfl⟩, ?_⟩
    rw [← map_smul]
    exact left_ne_zero_of_mul h
  · intro h
    apply h0
    ext w
    have h := congrFun h (φ.symm w)
    simp only [Pi.zero_apply, LinearEquiv.apply_symm_apply] at h ⊢
    exact (mul_eq_zero.1 h).resolve_right (Complex.exp_ne_zero _)
  · intro i z
    have hm : φ (Pi.single i 1) ∈ Λ := by
      refine (hΛ _).2 ⟨Pi.single i 1, 0, ?_⟩
      ext a
      by_cases h : a = i
      · subst h; simp [Matrix.mulVec, dotProduct]
      · simp [h, Matrix.mulVec, dotProduct]
    have e := hf ⟨_, hm⟩ (φ z)
    rw [h1 i ⟨_, hm⟩ z rfl] at e
    simp only [map_add (f := _)]
    rw [e, ← Complex.exp_nat_mul, mul_right_comm, ← Complex.exp_add, mul_comm]
    congr 2
    ring
  · intro j z
    have hm : φ (τ.mulVec (Pi.single j 1)) ∈ Λ := by
      refine (hΛ _).2 ⟨0, Pi.single j 1, ?_⟩
      have : (fun i => (((Pi.single j 1 : Fin g → ℤ) i : ℤ) : ℂ)) = Pi.single j 1 := by
        ext a
        by_cases h : a = j
        · subst h; simp
        · simp [h]
      rw [this]
      ext a
      simp
    have e := hf ⟨_, hm⟩ (φ z)
    rw [h2 j ⟨_, hm⟩ z rfl] at e
    simp only [map_add (f := _)]
    rw [e, mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    have : cexp (n * (Q (z + τ.mulVec (Pi.single j 1)) - Q z)) *
        cexp (-(n * Q (z + τ.mulVec (Pi.single j 1)))) = cexp (-(n * Q z)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [← this, show (n : ℂ) * (-(2 * Real.pi * I) * z j) = -(2 * Real.pi * I) * n * z j by ring]
    ring

theorem exists_ne_zero_of_selfDual : ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (g : ℕ) (B : LinearMap.BilinForm ℚ V) (p : V →ₗ[ℤ] (Fin g → ℂ)), Function.Injective p → ∀ L : Submodule ℤ V, L.FG → (∀ x, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, B x y = k) → Submodule.span ℝ (p '' (L : Set V)) = ⊤ → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ u v, (p u ⬝ᵥ Hm.mulVec (star (p v))).im = (B u v : ℝ)) → ∀ c : V → ℂ, (∀ v, ‖c v‖ = 1) → ∀ N : ℕ, 2 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, Differentiable ℂ f → f ≠ 0 → (∀ v ∈ L, ∀ z, f (z + p v) = c v * cexp (N * (Real.pi * (z ⬝ᵥ Hm.mulVec (star (p v))) + Real.pi / 2 * (p v ⬝ᵥ Hm.mulVec (star (p v))))) * f z) → ∃ v ∈ L, f ((N : ℂ)⁻¹ • p v) ≠ 0 := by
  intro V _ _ _ g B p hp L hfg hL hsp Hm hH hpos hB c hc N hN f hdf h0 hf
  set Λ : Submodule ℤ (Fin g → ℂ) := L.map p with hΛ
  have hsp' : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ := hsp
  choose q hq hpq using fun l : Λ => l.2
  have hint : ∀ l m : Λ, ∃ k : ℤ,
      (k : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im := fun l m => by
    obtain ⟨k, hk⟩ := (hL _).1 (hq l) _ (hq m)
    exact ⟨k, by rw [← hpq l, ← hpq m, hB, hk, Rat.cast_intCast]⟩
  choose k hk using hint
  let Ef : LinearMap.BilinForm ℤ Λ := LinearMap.mk₂ ℤ k
    (fun a b m => Int.cast_injective (α := ℝ) (by
      rw [Int.cast_add, hk, hk, hk, Submodule.coe_add, add_dotProduct, add_im]))
    (fun t a m => Int.cast_injective (α := ℝ) (by
      rw [smul_eq_mul, Int.cast_mul, hk, hk, Submodule.coe_smul, smul_dotProduct]; simp))
    (fun m a b => Int.cast_injective (α := ℝ) (by
      rw [Int.cast_add, hk, hk, hk, Submodule.coe_add, star_add, mulVec_add, dotProduct_add,
        add_im]))
    (fun t m a => Int.cast_injective (α := ℝ) (by
      rw [smul_eq_mul, Int.cast_mul, hk, hk, Submodule.coe_smul, star_smul, mulVec_smul,
        dotProduct_smul]; simp))
  have hE : ∀ l m : Λ, (Ef l m : ℝ) =
      ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im := hk
  have hker : ∀ l : Λ, Ef l = 0 → l = 0 := fun l hl =>
    Subtype.ext (eq_zero_of_im_eq_zero hpos hsp' fun m hm => by
      rw [← hE l ⟨m, hm⟩, hl]; simp)
  have hdisc : DiscreteTopology Λ := by
    haveI : Module.Finite ℤ Λ := Module.Finite.iff_fg.2 (hfg.map p)
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := Λ)
    refine discreteTopology_of_isOpen_singleton_zero ?_
    have e : ({0} : Set Λ) = ⋂ m ∈ s, {l : Λ |
        |((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im| < 1} := by
      ext l
      simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
      refine ⟨fun h m _ => by simp [h], fun h => hker l (LinearMap.ext_on hs fun m hm => ?_)⟩
      have h1 := h m hm
      rw [← hE, ← Int.cast_abs, ← Int.cast_one, Int.cast_lt] at h1
      exact Int.abs_lt_one_iff.1 h1
    rw [e]
    refine isOpen_biInter_finset fun m _ => isOpen_lt ?_ continuous_const
    refine (Complex.continuous_im.comp ?_).abs
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp continuous_subtype_val).mul continuous_const
  have hBinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).2 fun u hu => hp ?_
    rw [map_zero]
    refine eq_zero_of_im_eq_zero hpos hsp ?_
    rintro _ ⟨v, -, rfl⟩
    rw [hB, hu]; simp
  have hBsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℚ) (V := V)).symm).1 hBinj
  have hbij : Function.Bijective Ef := by
    refine ⟨(injective_iff_map_eq_zero Ef).2 hker, fun φ => ?_⟩
    obtain ⟨ψ, hψ⟩ := (Module.Baer.of_divisible ℚ).extension_property L.subtype
      L.subtype_injective ((Algebra.linearMap ℤ ℚ) ∘ₗ φ ∘ₗ p.submoduleMap L)
    obtain ⟨x, hx⟩ := hBsurj ψ.toAddMonoidHom.toRatLinearMap
    have h1 : ∀ (y) (hy : y ∈ L), B x y = (φ ⟨p y, Submodule.mem_map_of_mem hy⟩ : ℤ) :=
      fun y hy => by
        rw [hx]
        exact LinearMap.congr_fun hψ ⟨y, hy⟩
    refine ⟨⟨p x, Submodule.mem_map_of_mem ((hL x).2 fun y hy => ⟨_, h1 y hy⟩)⟩,
      LinearMap.ext ?_⟩
    rintro ⟨_, y, hy, rfl⟩
    refine Int.cast_injective (α := ℝ) ?_
    rw [hE, hB, h1 y hy, Rat.cast_intCast]
  have hN0 : N ≠ 0 := by omega
  choose χ hχ using fun l : Λ => IsAlgClosed.exists_pow_nat_eq (c (q l)) (Nat.pos_of_ne_zero hN0)
  have hχ1 : ∀ l, ‖χ l‖ = 1 := fun l =>
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN0).1 (by rw [← norm_pow, hχ, hc])
  obtain ⟨_, ⟨v, hv, rfl⟩, h⟩ := exists_ne_zero_of_principal Λ hdisc hsp' Hm χ Ef hH hpos hχ1 hE
    hbij N hN f hdf h0 (fun l z => by
      rw [mul_pow, hχ, ← Complex.exp_nat_mul, ← hpq l]
      exact hf _ (hq l) z)
  exact ⟨v, hv, h⟩

end GlobalTheory.ThetaDivisionPoints
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionNeZeroAtDivisionPointSelfDualStatement

section

@[expose] public section

open Complex Matrix

theorem _root_.GlobalTheory.T.thetaFunction_ne_zero_at_divisionPoint_selfDual : ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (g : ℕ) (B : LinearMap.BilinForm ℚ V) (p : V →ₗ[ℤ] (Fin g → ℂ)), Function.Injective p → ∀ L : Submodule ℤ V, L.FG → (∀ x, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, B x y = k) → Submodule.span ℝ (p '' (L : Set V)) = ⊤ → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ u v, (p u ⬝ᵥ Hm.mulVec (star (p v))).im = (B u v : ℝ)) → ∀ c : V → ℂ, (∀ v, ‖c v‖ = 1) → ∀ N : ℕ, 2 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, Differentiable ℂ f → f ≠ 0 → (∀ v ∈ L, ∀ z, f (z + p v) = c v * cexp (N * (Real.pi * (z ⬝ᵥ Hm.mulVec (star (p v))) + Real.pi / 2 * (p v ⬝ᵥ Hm.mulVec (star (p v))))) * f z) → ∃ v ∈ L, f ((N : ℂ)⁻¹ • p v) ≠ 0 := by
  first | exact @GlobalTheory.ThetaDivisionPoints.exists_ne_zero_of_selfDual | exact GlobalTheory.ThetaDivisionPoints.exists_ne_zero_of_selfDual | (intros; apply GlobalTheory.ThetaDivisionPoints.exists_ne_zero_of_selfDual <;> assumption)
end
end
