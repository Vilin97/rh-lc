module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Exc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Final
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Rootdeg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Layerex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Logs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Point2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Rootdeg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Vvat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Layeremb

section

@[expose] public section

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.layeremb :
    ∀ (l j N : ℕ), l.Prime → 0 < N → ∀ (L₀ L₁ : Type) [Field L₀] [NumberField L₀] [Field L₁] [NumberField L₁]
      [Algebra L₀ L₁], Nonempty (L₀ →ₐ[ℚ] CyclotomicField N ℚ) → IsLayer l j L₀ L₁ →
        ∃ N' : ℕ, 0 < N' ∧ N' ≤ 2 * Module.finrank ℚ L₁ * N ∧ Nonempty (L₁ →ₐ[ℚ] CyclotomicField N' ℚ) := by
  intro l j N hl hN L₀ L₁ _ _ _ _ _ ⟨f⟩ ⟨⟨k, hk⟩, _⟩
  have hlk : 0 < l ^ k := pow_pos hl.pos k
  have hM : 0 < l ^ k * N := Nat.mul_pos hlk hN
  haveI : NeZero (l ^ k) := ⟨hlk.ne'⟩
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast hN.ne'⟩
  haveI : NeZero ((l ^ k * N : ℕ) : ℚ) := ⟨by exact_mod_cast hM.ne'⟩
  refine ⟨l ^ k * N, hM, ?_, ?_⟩
  · exact Nat.mul_le_mul_right N (rootdeg L₁ l k hl ⟨_, IsCyclotomicExtension.zeta_spec (l ^ k) L₀ L₁⟩)
  · obtain ⟨ζ, hζ⟩ := @IsCyclotomicExtension.exists_isPrimitiveRoot _ ℚ (CyclotomicField (l ^ k * N) ℚ) _ _ _
      (CyclotomicField.isCyclotomicExtension _ ℚ) _ (Set.mem_singleton _) hM.ne'
    have hN' := hζ.pow hM rfl
    have hl' := hζ.pow hM (Nat.mul_comm _ _)
    have i2 := @IsCyclotomicExtension.isSplittingField_X_pow_sub_one N _ ℚ (CyclotomicField N ℚ) _ _ _
      (CyclotomicField.isCyclotomicExtension N ℚ)
    let e : CyclotomicField N ℚ →+* CyclotomicField (l ^ k * N) ℚ :=
      (@Polynomial.IsSplittingField.lift (CyclotomicField (l ^ k * N) ℚ) ℚ (CyclotomicField N ℚ) _ _ _ _ _
        (Polynomial.X ^ N - 1) i2 (by simpa using Polynomial.X_pow_sub_one_splits hN')).toRingHom
    letI : Algebra L₀ (CyclotomicField (l ^ k * N) ℚ) := (e.comp f.toRingHom).toAlgebra
    haveI := IsCyclotomicExtension.isSplittingField_X_pow_sub_one (l ^ k) L₀ L₁
    let h : L₁ →ₐ[L₀] CyclotomicField (l ^ k * N) ℚ :=
      Polynomial.IsSplittingField.lift _ (Polynomial.X ^ (l ^ k) - 1)
        (by simpa using Polynomial.X_pow_sub_one_splits hl')
    exact ⟨h.toRingHom.toRatAlgHom⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Layerdisc

section

@[expose] public section

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.layerdisc :
    ∀ (l j n1 N0 : ℕ), l.Prime → 0 < N0 → ∃ (n0 : ℕ) (c0 : ℝ), 0 ≤ c0 ∧
      ∀ (P : ℕ) (w : ℝ), 0 < P → 1 ≤ w → Real.log (P : ℝ) ≤ w →
        ∀ (L₀ L₁ : Type) [Field L₀] [NumberField L₀] [Field L₁] [NumberField L₁] [Algebra L₀ L₁],
          Module.finrank ℚ L₀ ≤ n1 → Nonempty (L₀ →ₐ[ℚ] CyclotomicField (N0 * P) ℚ) → IsLayer l j L₀ L₁ →
            Module.finrank ℚ L₁ ≤ n0 ∧ Real.log (2 * ((discr L₁).natAbs : ℝ)) ≤ c0 * w := by
  intro l j n1 N0 hl hN0
  have hlj : 1 ≤ l ^ j := Nat.one_le_pow _ _ hl.pos
  set n0 : ℕ := (n1 + 1) * l ^ j with hn0
  have hn0pos : 1 ≤ n0 := by
    rw [hn0]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hn0R : (1:ℝ) ≤ (n0:ℝ) := by exact_mod_cast hn0pos
  have hN0R : (1:ℝ) ≤ (N0:ℝ) := by exact_mod_cast hN0
  have hC1 : (1:ℝ) ≤ 2 * (n0:ℝ) * (N0:ℝ) := by nlinarith
  have hlogC : 0 ≤ Real.log (2 * (n0:ℝ) * (N0:ℝ)) := Real.log_nonneg hC1
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  set A : ℝ := Real.log 2 + (n0:ℝ) * Real.log (2 * (n0:ℝ) * (N0:ℝ)) with hA
  have hA0 : 0 ≤ A := by
    have : 0 ≤ (n0:ℝ) * Real.log (2 * (n0:ℝ) * (N0:ℝ)) := mul_nonneg (by linarith) hlogC
    linarith
  refine ⟨n0, A + n0, by linarith, ?_⟩
  intro P w hP hw hlogP L₀ L₁ _ _ _ _ _ hdeg hemb hlay
  have hdim : Module.finrank ℚ L₀ * Module.finrank L₀ L₁ = Module.finrank ℚ L₁ :=
    Module.finrank_mul_finrank ℚ L₀ L₁
  have hrel : Module.finrank L₀ L₁ = l ^ j := by
    unfold IsLayer at hlay
    exact hlay.2
  have hd1 : Module.finrank ℚ L₁ ≤ n0 := by
    rw [← hdim, hrel, hn0]
    exact Nat.mul_le_mul_right _ (by omega)
  refine ⟨hd1, ?_⟩
  have hNP : 0 < N0 * P := Nat.mul_pos hN0 hP
  obtain ⟨N', hN'pos, hN'le, hN'emb⟩ := layeremb l j (N0 * P) hl hNP L₀ L₁ hemb hlay
  have hdisc := disc L₁ N' hN'pos hN'emb
  have hd1R : ((Module.finrank ℚ L₁ : ℕ) : ℝ) ≤ (n0:ℝ) := by exact_mod_cast hd1
  have hPR : (1:ℝ) ≤ (P:ℝ) := by exact_mod_cast hP
  have hN'R : (1:ℝ) ≤ (N':ℝ) := by exact_mod_cast hN'pos
  have hlogN' : 0 ≤ Real.log (N':ℝ) := Real.log_nonneg hN'R
  have hN'le' : (N':ℝ) ≤ 2 * (n0:ℝ) * (N0:ℝ) * (P:ℝ) := by
    have h1 : (N':ℝ) ≤ ((2 * Module.finrank ℚ L₁ * (N0 * P) : ℕ) : ℝ) := by exact_mod_cast hN'le
    have h2 : ((2 * Module.finrank ℚ L₁ * (N0 * P) : ℕ) : ℝ) ≤ 2 * (n0:ℝ) * (N0:ℝ) * (P:ℝ) := by
      push_cast
      have : (0:ℝ) ≤ (N0:ℝ) * (P:ℝ) := by positivity
      nlinarith
    linarith
  have hlogle : Real.log (N':ℝ) ≤ Real.log (2 * (n0:ℝ) * (N0:ℝ)) + Real.log (P:ℝ) := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    exact Real.log_le_log (by linarith) hN'le'
  have hLP0 : 0 ≤ Real.log (P:ℝ) := Real.log_nonneg hPR
  have hlog2D : Real.log (2 * ((discr L₁).natAbs : ℝ)) ≤ Real.log 2 + Real.log ((discr L₁).natAbs : ℝ) := by
    rcases Nat.eq_zero_or_pos (discr L₁).natAbs with h | h
    · rw [h]
      simpa using hlog2
    · have hD : ((discr L₁).natAbs : ℝ) ≠ 0 := by positivity
      rw [Real.log_mul (by norm_num) hD]
  have k1 : ((Module.finrank ℚ L₁ : ℕ) : ℝ) * Real.log (N':ℝ) ≤ (n0:ℝ) * Real.log (N':ℝ) :=
    mul_le_mul_of_nonneg_right hd1R hlogN'
  have k2 : (n0:ℝ) * Real.log (N':ℝ) ≤ (n0:ℝ) * (Real.log (2 * (n0:ℝ) * (N0:ℝ)) + Real.log (P:ℝ)) :=
    mul_le_mul_of_nonneg_left hlogle (by linarith)
  have k3 : (n0:ℝ) * Real.log (P:ℝ) ≤ (n0:ℝ) * w := mul_le_mul_of_nonneg_left hlogP (by linarith)
  have k4 : A ≤ A * w := by nlinarith
  nlinarith
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.PartA

section

@[expose] public section

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

private theorem ne_top_and_toNat_le_of_le_one_add (a b : ℕ∞) (hb : b ≠ ⊤) (h : a ≤ 1 + b) :
    a ≠ ⊤ ∧ a.toNat ≤ 1 + b.toNat := by
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hb
  have h' : a ≤ ((1 + n : ℕ) : ℕ∞) := by push_cast; exact h
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) h'
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp ha
  refine ⟨ha, ?_⟩
  simp only [ENat.toNat_coe]
  exact_mod_cast h'

theorem UpperTheory.V.Win.partA :
    ∀ CK : ℝ, 0 < CK → LemmaK CK → ∀ (M : AbF) (R : ℕ) (J Ct eps A1 : ℝ), 0 < J → 0 ≤ Ct → 0 < eps →
      ∃ x0 : ℝ, ∀ e t : ℝ → ℕ, admitted A1 Ct e t → ∀ (X : ℝ) (q d : ℕ), PrimePair M.m q d →
        Real.log ((q : ℝ) * d) ≤ X ^ (eps / (4 * J)) →
        ∀ (L₀ : Type) [Field L₀] [NumberField L₀], TwoBase M q d L₀ → ABound 2 R L₀ →
          ∃ Exc : Finset ℕ, Exc.card ≤ R ∧ ∀ x ≥ x0, X ^ (1 / J) ≤ x → x ≤ X → Good (eps / (2 * CK)) Ct Exc x →
            BaAt M eps e t q d x := by
  intro CK hCK hK M R J Ct eps A1 hJ hCt heps
  obtain ⟨n0, c0, hc0, hLD⟩ := layerdisc 2 (jZero 2 R) (8 * M.deg) (4 * M.m) Nat.prime_two
    (by have := M.pos; omega)
  obtain ⟨C, hC0, hC⟩ := point2 CK hCK hK 2 R (16 * M.deg) n0 c0 J Ct eps (2 * |A1| + 2)
    hc0 hJ hCt heps (by positivity)
  obtain ⟨x0, hx02, hx0⟩ := final Ct eps C heps
  refine ⟨x0, fun e t hAdm X q d hPP hlogqd L₀ _ _ hTB hAB => ?_⟩
  obtain ⟨hmu, hfin, hcyc, hE⟩ := hTB
  have hSB : SecondBound 2 R L₀ := hAB.2
  obtain ⟨c, hζ, hZ⟩ := exc 2 R L₀ hAB
  have hc : c ≤ 16 * M.deg := by
    have h1 := rootdeg L₀ 2 c Nat.prime_two hζ
    have h2 : c < 2 ^ c := Nat.lt_two_pow_self
    omega
  obtain ⟨L₂, i1, i2, i3, hL₂⟩ := layerex 2 (jZero 2 R) Nat.prime_two L₀ hmu
  obtain ⟨Exc, hExc⟩ := hZ ⌊X ^ Ct⌋₊
  refine ⟨Exc, hExc.1, fun x hx hXx hxX hG E _ _ hEc => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  obtain ⟨he2, h2e, -, htx⟩ := hAdm x (by linarith)
  have hw : (1 : ℝ) ≤ x ^ (eps / 4) := Real.one_le_rpow hx1 (by positivity)
  have hP : 0 < q * d := Nat.mul_pos hPP.1.pos hPP.2.2.1.pos
  have hlogP : Real.log ((q * d : ℕ) : ℝ) ≤ x ^ (eps / 4) := by
    push_cast
    exact hlogqd.trans (logs.2.1 J eps X x hJ heps hX1 hXx)
  have hcyc' : Nonempty (L₀ →ₐ[ℚ] CyclotomicField (4 * M.m * (q * d)) ℚ) := by
    rw [← mul_assoc]; exact hcyc
  obtain ⟨hn0, hdisc⟩ := hLD (q * d) (x ^ (eps / 4)) hP hw hlogP L₀ L₂ hfin hcyc' hL₂
  obtain ⟨m, L₁, j1, j2, j3, hL₁, hme, hsha⟩ := hE (e x) he2 E hEc
  have hm : (m : ℝ) ≤ (2 * |A1| + 2) * (1 + Real.log x) := by
    have h3 := logs.2.2 (e x) A1 x hx1 h2e
    have h4 : (m : ℝ) ≤ (e x : ℝ) + 2 := by exact_mod_cast hme
    linarith
  have hpb : 0 ≤ ptBound C eps x := by
    show 0 ≤ C * (1 + Real.log x) + 2 * Real.exp (C * x ^ (3 * eps / 4))
    exact add_nonneg (mul_nonneg hC0 (by linarith)) (by positivity)
  show VVat 2 E (t x) (Real.exp (x ^ (4 * eps / 5)))
  refine vvat 2 (t x) E (x ^ Ct) (ptBound C eps x) _ hpb htx (hx0 x hx) ?_
  intro k hk1 hkt
  have hkx : (k : ℝ) ≤ x ^ Ct := le_trans (by exact_mod_cast hkt.le) htx
  have hk := hC L₀ hmu hSB c X Exc hc hExc L₂ hL₂ hn0 x hx1 hXx hxX hG hdisc k hk1 hkx
    m L₁ hL₁ hm
  obtain ⟨hne, hle⟩ := ne_top_and_toNat_le_of_le_one_add _ _ hk.1 (hsha k hk1)
  refine ⟨hne, ?_⟩
  have h5 : ((shaInv E 2 k).toNat : ℝ) ≤ 1 + ((shaInv L₁ 2 k).toNat : ℝ) := by
    exact_mod_cast hle
  linarith [hk.2]
end
end
