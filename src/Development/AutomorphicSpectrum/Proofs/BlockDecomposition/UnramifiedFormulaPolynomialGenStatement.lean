module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardPreimageHom
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedNondeg
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianRepCountFourierExpansion
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeriesEqDens
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCharacterOrthogonality

section

@[expose] public section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.SiegLoc.HermOrth

variable {R : Type} [CommRing R]

theorem red_add' (ϖ : R) (k : ℕ) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    red ϖ k (x + y) = red ϖ k x + red ϖ k y := by
  ext i j
  simp [red]

theorem red_neg' (ϖ : R) (k : ℕ) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    red ϖ k (-x) = -red ϖ k x := by
  ext i j
  simp [red]

theorem cT_add' (σ : R →+* R) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    cT σ (x + y) = cT σ x + cT σ y := by
  ext i j
  simp [cT]

theorem cT_neg' (σ : R →+* R) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    cT σ (-x) = -cT σ x := by
  ext i j
  simp [cT]

theorem cT_single' (σ : R →+* R) {n : ℕ} (i j : Fin n) (c : R) :
    cT σ (Matrix.single i j c) = Matrix.single j i (σ c) := by
  simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.map_single, Matrix.transpose_single]

theorem trace_single_mul' {n : ℕ} (i j : Fin n) (c : R) (y : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (Matrix.single i j c * y) = c * y j i := by
  rw [Matrix.trace_single_mul, smul_eq_mul]

theorem trace_red_mul (ϖ : R) (k n : ℕ) (b y : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (red ϖ k b * red ϖ k y) = Ideal.Quotient.mk (lev ϖ k) (Matrix.trace (b * y)) := by
  unfold PositivityTheory.PfSWUS.Loc.red
  rw [← Matrix.map_mul]

  simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, map_sum]

theorem tsum_eq_zero_of_shift {G : Type} [AddCommGroup G] (H : Set G)
    (hadd : ∀ a b, a ∈ H → b ∈ H → a + b ∈ H) (hneg : ∀ a, a ∈ H → -a ∈ H)
    (f : G → ℂ) (hf : ∀ a b, f (a + b) = f a * f b) (B₀ : G) (hB₀ : B₀ ∈ H) (h : f B₀ ≠ 1) :
    ∑' B : H, f B.1 = 0 := by
  let e : H ≃ H :=
    { toFun := fun B => ⟨B₀ + B.1, hadd _ _ hB₀ B.2⟩
      invFun := fun B => ⟨-B₀ + B.1, hadd _ _ (hneg _ hB₀) B.2⟩
      left_inv := fun B => Subtype.ext (by simp)
      right_inv := fun B => Subtype.ext (by simp) }
  have key : ∑' B : H, f B.1 = f B₀ * ∑' B : H, f B.1 := by
    calc ∑' B : H, f B.1 = ∑' B : H, f (e B).1 := (e.tsum_eq (fun B : H => f B.1)).symm
      _ = ∑' B : H, f B₀ * f B.1 := tsum_congr fun B => by
          show f (B₀ + B.1) = _
          exact hf _ _
      _ = f B₀ * ∑' B : H, f B.1 := tsum_mul_left
  have hzero : (f B₀ - 1) * ∑' B : H, f B.1 = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.mp hzero with h' | h'
  · exact absurd (sub_eq_zero.mp h') h
  · exact h'

theorem hermMod_add {σ : R →+* R} {ϖ : R} {n k : ℕ}
    (a b : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) (ha : a ∈ hermMod σ ϖ n k)
    (hb : b ∈ hermMod σ ϖ n k) : a + b ∈ hermMod σ ϖ n k := by
  unfold PositivityTheory.PfSWUS.Loc.hermMod at ha hb ⊢
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  have ha'' : PositivityTheory.PfSWUS.Loc.cT σ a' = a' := ha'
  have hb'' : PositivityTheory.PfSWUS.Loc.cT σ b' = b' := hb'
  refine ⟨a' + b', ?_, GlobalTheory.CompanionTheory.SiegLoc.HermOrth.red_add' _ _ _ _⟩
  show PositivityTheory.PfSWUS.Loc.cT σ (a' + b') = a' + b'
  rw [GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_add', ha'', hb'']

theorem hermMod_neg {σ : R →+* R} {ϖ : R} {n k : ℕ}
    (a : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) (ha : a ∈ hermMod σ ϖ n k) :
    -a ∈ hermMod σ ϖ n k := by
  unfold PositivityTheory.PfSWUS.Loc.hermMod at ha ⊢
  obtain ⟨a', ha', rfl⟩ := ha
  have ha'' : PositivityTheory.PfSWUS.Loc.cT σ a' = a' := ha'
  refine ⟨-a', ?_, GlobalTheory.CompanionTheory.SiegLoc.HermOrth.red_neg' _ _ _⟩
  show PositivityTheory.PfSWUS.Loc.cT σ (-a') = -a'
  rw [GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_neg', ha'']

theorem red_eq_zero_of_trivial {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
    {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hR : IsUnrQuad R σ ϖ q ε) (hψ : IsLevelChars σ ϖ ψ)
    (n k : ℕ) (y : Matrix (Fin n) (Fin n) R) (hy : cT σ y = y)
    (h : ∀ b : Matrix (Fin n) (Fin n) R, cT σ b = b →
      ψ k (Ideal.Quotient.mk _ (Matrix.trace (b * y))) = 1) :
    red ϖ k y = 0 := by
  have hσσ : ∀ a, σ (σ a) = a := hR.1
  ext i j
  simp only [PositivityTheory.PfSWUS.Loc.red, Matrix.map_apply, Matrix.zero_apply]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  apply GlobalTheory.CompanionTheory.SiegLoc.trace_nondeg hR hψ k (y i j)
  intro t
  have hyji : σ (y i j) = y j i := by
    have hentry := congrFun (congrFun hy j) i
    simpa [PositivityTheory.PfSWUS.Loc.cT] using hentry
  have hb : PositivityTheory.PfSWUS.Loc.cT σ (Matrix.single j i t + Matrix.single i j (σ t)) =
      Matrix.single j i t + Matrix.single i j (σ t) := by
    rw [GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_add', GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_single', GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_single',
      hσσ, add_comm]
  have htr := h _ hb
  rw [Matrix.add_mul, Matrix.trace_add, GlobalTheory.CompanionTheory.SiegLoc.HermOrth.trace_single_mul',
    GlobalTheory.CompanionTheory.SiegLoc.HermOrth.trace_single_mul'] at htr
  rw [map_mul σ, hyji]
  exact htr

theorem orth_hermMod (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ)
    (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)]
    (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ) (hψ : IsLevelChars σ ϖ ψ) (n k : ℕ)
    (Y : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) (hY : Y ∈ hermMod σ ϖ n k) :
    (Y = 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) =
        (Nat.card (hermMod σ ϖ n k) : ℂ)) ∧
      (Y ≠ 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) = 0) := by
  refine ⟨fun h0 => ?_, fun hne => ?_⟩
  · subst h0
    simp only [Matrix.mul_zero, Matrix.trace_zero, AddChar.map_zero_eq_one]
    rw [tsum_const, nsmul_eq_mul, mul_one]
  · have hY' := hY
    unfold PositivityTheory.PfSWUS.Loc.hermMod at hY'
    obtain ⟨y, hy, rfl⟩ := hY'
    by_contra hsum
    apply hne
    apply GlobalTheory.CompanionTheory.SiegLoc.HermOrth.red_eq_zero_of_trivial hR hψ n k y hy
    intro b hb
    rw [← GlobalTheory.CompanionTheory.SiegLoc.HermOrth.trace_red_mul]
    by_contra hb1
    exact hsum (GlobalTheory.CompanionTheory.SiegLoc.HermOrth.tsum_eq_zero_of_shift _
      (fun a₁ a₂ h₁ h₂ => GlobalTheory.CompanionTheory.SiegLoc.HermOrth.hermMod_add a₁ a₂ h₁ h₂)
      (fun a₁ h₁ => GlobalTheory.CompanionTheory.SiegLoc.HermOrth.hermMod_neg a₁ h₁)
      (fun B => ψ k (Matrix.trace (B * PositivityTheory.PfSWUS.Loc.red ϖ k y)))
      (fun a₁ a₂ => by simp only [Matrix.add_mul, Matrix.trace_add, AddChar.map_add_eq_mul])
      (PositivityTheory.PfSWUS.Loc.red ϖ k b) ⟨b, hb, rfl⟩ hb1)

end GlobalTheory.CompanionTheory.SiegLoc.HermOrth
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFormulaPolynomialGen

section

@[expose] public section

noncomputable section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.LocalDens Filter Topology Polynomial

namespace GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries

variable {R : Type} [CommRing R]

theorem densAt_succ {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hU : IsUnrQuad R σ ϖ q ε) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (hS : IsUnimod σ S) (hT : IsUnimod σ T) (b : ℕ) :
    densAt σ ϖ S T (0 + b + 1) = densAt σ ϖ S T (0 + b + 1 + 1) := by
  obtain ⟨hTc, hdet⟩ := hT
  obtain ⟨c, hc⟩ : ∃ c, c * T.det = ϖ ^ 0 := by
    obtain ⟨w, hw⟩ := hdet.exists_left_inv
    exact ⟨w, by simpa using hw⟩
  have hσ := hU.fix_ϖ
  have hfin : ∀ k, Finite (R ⧸ lev ϖ k) := fun k => finite_lev (by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hU.card]
    exact pow_ne_zero _ (by have := hU.one_lt; omega)) k
  have h1 : T * (c • T.adjugate) = ϖ ^ 0 • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hc]
  have h2 : cT σ (c • T.adjugate) * T = ϖ ^ 0 • (1 : Matrix (Fin n) (Fin n) R) := by
    have := congrArg (cT σ) h1
    rw [cT_mul, hTc, cT_smul σ (ϖ ^ 0), cT_one, map_pow, hσ] at this
    exact this
  obtain ⟨t, ht⟩ : ∃ t, t + σ t = 1 := by
    obtain ⟨u, hu, -⟩ := hU.basis
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h3 : (u - σ u) * σ w = -1 := by
      have := congrArg σ hw
      simp only [map_mul, map_sub, hU.inv, map_one] at this
      linear_combination -this
    have h4 : σ w = -w := by linear_combination (-σ w) * hw + w * h3
    refine ⟨u * w, ?_⟩
    rw [map_mul, h4]
    linear_combination hw
  refine dens_step hfin hU.inv hσ S T _ hS.1 hTc (fun h hh hk => ?_)
  rw [red_eq_iff] at hk
  choose C hC using hk
  have hhT : h = T + ϖ ^ (0 + b + 1) • Matrix.of C := by
    ext i j
    have := hC i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← this]; ring
  have hCh : cT σ (Matrix.of C) = Matrix.of C := by
    ext i j
    have e1 := congrFun (congrFun (hh) i) j
    have e2 := congrArg σ (hC j i)
    have e3 := congrFun (congrFun hTc i) j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply] at e1 e3
    simp only [map_sub, map_mul, map_pow, hσ, e1, e3] at e2
    have := (hU.reg.pow (0 + b + 1)) (a₁ := σ (C j i)) (a₂ := C i j) (by
      simp only [smul_eq_mul]
      rw [← e2, hC i j])
    simpa [cT] using this
  obtain ⟨g, h', hgh, hhg, hg⟩ := twist hσ ht hCh 0 b h1 h2
  rw [← hhT] at hg
  rw [solCount_eq, ← sol_congr σ ϖ S _ hg, ← solCount_eq]
  exact solCount_congr hσ S T g h' _ hgh hhg

theorem densAt_eq_densAt_one_of_isUnimod {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hU : IsUnrQuad R σ ϖ q ε) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (hS : IsUnimod σ S) (hT : IsUnimod σ T)
    (k : ℕ) (hk : 1 ≤ k) : densAt σ ϖ S T k = densAt σ ϖ S T 1 := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    obtain ⟨b, rfl⟩ : ∃ b, k = 0 + b + 1 := ⟨k - 1, by omega⟩
    rw [← densAt_succ hU S T hS hT b, ih]

theorem densAt_eq_of_isDens {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hU : IsUnrQuad R σ ϖ q ε) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (hS : IsUnimod σ S) (hT : IsUnimod σ T)
    {α : ℝ} (hα : IsDens σ ϖ S T α) (k : ℕ) (hk : 1 ≤ k) : densAt σ ϖ S T k = α := by
  have h1 : Tendsto (densAt σ ϖ S T) atTop (𝓝 (densAt σ ϖ S T 1)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact (densAt_eq_densAt_one_of_isUnimod hU S T hS hT j hj).symm
  rw [densAt_eq_densAt_one_of_isUnimod hU S T hS hT k hk]
  exact tendsto_nhds_unique h1 hα

theorem isUnimod_one (σ : R →+* R) (m : ℕ) : IsUnimod σ (1 : Matrix (Fin m) (Fin m) R) :=
  ⟨cT_one σ, by simp⟩

theorem unrPoly : PositivityTheory.PfSWUS.Loc.UnrFormula → PositivityTheory.SiegelWeilFormula.Gen.UnrPoly := by
  intro hF R _ σ ϖ q ε hR ψ hψ n T hT k hk t
  classical
  have hfin : ∀ k, Finite (R ⧸ lev ϖ k) := fun k => finite_lev (by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hR.card]
    exact pow_ne_zero _ (by have := hR.one_lt; omega)) k
  letI : ∀ k, Fintype (R ⧸ lev ϖ k) := fun k => Fintype.ofFinite _
  haveI : Finite (Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) :=
    inferInstanceAs (Finite (Fin n → Fin n → R ⧸ lev ϖ k))
  haveI : Finite (hermMod σ ϖ n k) := Subtype.finite
  letI : Fintype (hermMod σ ϖ n k) := Fintype.ofFinite _
  have hq1 : 1 < q := hR.one_lt
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hε : (ε : ℂ) ^ 2 = 1 := by
    rcases hR.eps with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hnε : ‖(ε : ℂ)‖ = 1 := by
    rcases hR.eps with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  let P : ℂ[X] := ∑ B : hermMod σ ϖ n k,
    C (ψ k (Matrix.trace (red ϖ k T * B.1))) * X ^ Nat.log (q ^ 2) (nuAt ϖ B.1)
  let Q : ℂ[X] := ∏ i : Fin n, (1 - X * C (((ε : ℂ) * q) ^ (i : ℕ)))
  have hP : ∀ x : ℂ, P.eval x = ∑' B : hermMod σ ϖ n k,
      ψ k (Matrix.trace (red ϖ k T * B.1)) * x ^ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
    intro x
    rw [tsum_fintype]
    simp [P, Polynomial.eval_finsetSum]
  have hQ : ∀ x : ℂ, Q.eval x = ∏ i : Fin n, (1 - x * ((ε : ℂ) * q) ^ (i : ℕ)) := by
    intro x
    simp [Q, Polynomial.eval_prod]
  have hval : ∀ m, n ≤ m → P.eval (((ε : ℂ) / q) ^ m) = Q.eval (((ε : ℂ) / q) ^ m) := by
    intro m hm
    have hS := isUnimod_one σ m
    have hs : siegAt ϖ σ ψ q ε m T k = ((densAt σ ϖ (1 : Matrix (Fin m) (Fin m) R) T k : ℝ) : ℂ) :=
      GlobalTheory.CompanionTheory.SiegLoc.level_identity R σ ϖ q ε hR ψ hψ m n k 1 T hS.1 hT.1
        (GlobalTheory.CompanionTheory.SiegLoc.HermOrth.orth_hermMod R σ ϖ q ε hR ψ hψ n k)
        (fun B hB => GlobalTheory.CompanionTheory.SiegLoc.gauss_full hR hψ hε k 1 hS B hB)
    have hc : ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) = ((ε : ℂ) / q) ^ m := by
      rw [div_pow, zpow_neg, zpow_natCast, div_eq_mul_inv]
    rw [hP, hQ]
    unfold siegAt at hs
    rw [hc] at hs
    rw [hs, densAt_eq_of_isDens hR 1 T hS hT (hF R σ ϖ q ε hR m n hm 1 T hS hT) k hk]
    push_cast
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi : (i : ℕ) ≤ m := by have := i.2; omega
    have e1 : ((ε : ℂ) / q) ^ m = ((ε : ℂ) / q) ^ (m - (i : ℕ)) * ((ε : ℂ) / q) ^ (i : ℕ) := by
      rw [← pow_add, Nat.sub_add_cancel hi]
    have e2 : ((ε : ℂ) / q) ^ (i : ℕ) * ((ε : ℂ) * q) ^ (i : ℕ) = 1 := by
      rw [← mul_pow]
      have : (ε : ℂ) / q * ((ε : ℂ) * q) = 1 := by
        field_simp
        simpa using hε
      rw [this, one_pow]
    rw [e1, mul_assoc, e2, mul_one]
  have hinj : Function.Injective (fun j : ℕ => ((ε : ℂ) / q) ^ (n + j)) := by
    intro a b hab
    have h1 : ‖((ε : ℂ) / q) ^ (n + a)‖ = ‖((ε : ℂ) / q) ^ (n + b)‖ := congrArg norm hab
    have hnorm : ‖(ε : ℂ) / q‖ = (q : ℝ)⁻¹ := by
      rw [norm_div, hnε]
      simp
    rw [norm_pow, norm_pow, hnorm] at h1
    have hq0 : (0 : ℝ) < (q : ℝ)⁻¹ := by
      have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
      positivity
    have hq2 : (q : ℝ)⁻¹ ≠ 1 := by
      have : (1 : ℝ) < q := by exact_mod_cast hq1
      exact (inv_lt_one_of_one_lt₀ this).ne
    have := pow_right_injective₀ hq0 hq2 h1
    omega
  have hPQ : P = Q := Polynomial.eq_of_infinite_eval_eq P Q
    (Set.infinite_of_injective_forall_mem hinj fun j => hval (n + j) (by omega))
  have := congrArg (Polynomial.eval t) hPQ
  rw [hP, hQ] at this
  exact this

end GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFormulaPolynomialGenStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.unramified_formula_polynomial_gen : PositivityTheory.PfSWUS.Loc.UnrFormula → PositivityTheory.SiegelWeilFormula.Gen.UnrPoly := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries.unrPoly | exact GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries.unrPoly | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries.unrPoly <;> assumption)
end
end
