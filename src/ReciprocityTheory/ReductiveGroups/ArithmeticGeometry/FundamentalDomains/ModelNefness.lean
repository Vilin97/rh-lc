module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianLatticeMaps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Algebra.Order.Star.Real
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CompactEntryBounds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianPsiBounds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantNormalForms

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FiniteTranslateSets

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace FiniteTranslateSets

open NumberField Module

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def Sh (R : ℝ) : Set E :=
  {β | ∃ α : 𝓞 E, (α : E) = (X.den : E) * β ∧ ∀ σ : E →+* ℂ, ‖σ (α : E)‖ ≤ R}

theorem Sh_finite (R : ℝ) (hR : 0 ≤ R) : (Sh X R).Finite := by
  have hS := NumberField.Embeddings.finite_of_norm_le E ℂ R
  have hd : ((X.den : 𝓞 E) : E) ≠ 0 := by exact_mod_cast X.den_ne
  refine (hS.image fun x => x / (X.den : E)).subset ?_
  rintro β ⟨α, hα, hb⟩
  refine ⟨(α : E), ⟨α.isIntegral_coe, hb⟩, ?_⟩
  show (α : E) / (X.den : E) = β
  rw [hα]
  field_simp

def Sz (T : ℝ) : Set ℤ := {n | ((n : ℝ)) ^ 2 ≤ T}

theorem Sz_finite (T : ℝ) : (Sz T).Finite := by
  refine (Set.finite_Icc (-⌈T⌉) ⌈T⌉).subset ?_
  intro n hn
  have hn' : ((n : ℝ)) ^ 2 ≤ T := hn
  have h1 : |n| ≤ n ^ 2 := by
    rcases eq_or_ne n 0 with h | h
    · simp [h]
    · have h0 : 1 ≤ |n| := Int.one_le_abs h
      nlinarith [abs_mul_abs_self n, abs_nonneg n]
  have h2 : ((|n| : ℤ) : ℝ) ≤ T := by
    have h4 : ((|n| : ℤ) : ℝ) ≤ ((n ^ 2 : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at h4 ⊢
    linarith
  have h3 : |n| ≤ ⌈T⌉ := by exact_mod_cast h2.trans (Int.le_ceil T)
  exact Set.mem_Icc.mpr ⟨by linarith [neg_abs_le n], by linarith [le_abs_self n]⟩

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def TS (R T : ℝ) : Set ((ι → ι → E) × (Free.ChooseBasisIndex ℤ (𝓞 E) → ι → ι → ℤ)) :=
  {t | ∃ f : Basis ι ℤ X.Λ, ((∀ i j, (HermitianLatticeMaps.ty X f).1 i j ∈ Sh X R) ∧
    ∀ k i j, (HermitianLatticeMaps.ty X f).2 k i j ∈ Sz T) ∧ HermitianLatticeMaps.ty X f = t}

theorem TS_finite (R T : ℝ) (hR : 0 ≤ R) : (TS X (ι := ι) R T).Finite := by
  have hA : (Set.univ.pi fun _ : ι => Set.univ.pi fun _ : ι => Sh X R).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => Sh_finite X R hR
  have hB : (Set.univ.pi fun _ : Free.ChooseBasisIndex ℤ (𝓞 E) =>
      Set.univ.pi fun _ : ι => Set.univ.pi fun _ : ι => Sz T).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.Finite.pi fun _ => Sz_finite T
  refine (hA.prod hB).subset ?_
  rintro t ⟨f, ⟨h1, h2⟩, rfl⟩
  exact ⟨fun i _ j _ => h1 i j, fun k _ i _ j _ => h2 k i j⟩

end FiniteTranslateSets

end ReciprocityTheory.ChartRestriction.G.FD
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModelNefness

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

open Matrix NumberField Complex Module

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem reductionTheory_holds : MahlerCompactnessCriterion (E := E) := by
  unfold MahlerCompactnessCriterion
  intro r X ε hε
  classical
  have hm : (0:ℝ) < ε ^ 2 := by positivity
  have hB0 : (0:ℝ) ≤ 2 ^ (finrank ℤ X.Λ * (finrank ℤ X.Λ - 1)) *
      |(QuadraticLatticeForms.Bm X (RealPlaceEmbeddings.zb X)).det| / (ε ^ 2) ^ (finrank ℤ X.Λ - 1) := by positivity
  set B : ℝ := 2 ^ (finrank ℤ X.Λ * (finrank ℤ X.Λ - 1)) *
      |(QuadraticLatticeForms.Bm X (RealPlaceEmbeddings.zb X)).det| / (ε ^ 2) ^ (finrank ℤ X.Λ - 1) with hB_def
  have hC : 0 ≤ HermitianPsiBounds.Cinv X := HermitianPsiBounds.Cinv_nonneg (X := X)
  have hD : (0:ℝ) ≤ ∑ σ : E →+* ℂ, ‖σ (X.den : E)‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set D : ℝ := ∑ σ : E →+* ℂ, ‖σ (X.den : E)‖ with hD_def
  have hR : 0 ≤ D * ((B + B) * HermitianPsiBounds.Cinv X) := mul_nonneg hD (mul_nonneg (add_nonneg hB0 hB0) hC)
  set R : ℝ := D * ((B + B) * HermitianPsiBounds.Cinv X) with hR_def
  have hW : (0:ℝ) ≤ ∑ k : Free.ChooseBasisIndex ℤ (𝓞 E), ∑ τ : X.Ψ,
      ‖τ.1 ((RingOfIntegers.basis E k : 𝓞 E) : E)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  set W : ℝ := ∑ k : Free.ChooseBasisIndex ℤ (𝓞 E), ∑ τ : X.Ψ,
      ‖τ.1 ((RingOfIntegers.basis E k : 𝓞 E) : E)‖ ^ 2 with hW_def
  set T : ℝ := 9 ^ (finrank ℤ X.Λ) * (W * B) / ε ^ 2 with hT_def
  have hfin := FiniteTranslateSets.TS_finite (X := X) (ι := Fin (finrank ℤ X.Λ)) R T hR

  obtain ⟨rep, hrep⟩ : ∃ rep : _ → Basis (Fin (finrank ℤ X.Λ)) ℤ X.Λ,
      ∀ t ∈ FiniteTranslateSets.TS X (ι := Fin (finrank ℤ X.Λ)) R T, HermitianLatticeMaps.ty X (rep t) = t := by
    refine ⟨fun t => if h : ∃ f : Basis (Fin (finrank ℤ X.Λ)) ℤ X.Λ, HermitianLatticeMaps.ty X f = t
      then h.choose else RealPlaceEmbeddings.zb X, fun t ht => ?_⟩
    have h : ∃ f : Basis (Fin (finrank ℤ X.Λ)) ℤ X.Λ, HermitianLatticeMaps.ty X f = t := by
      simp only [FiniteTranslateSets.TS, Set.mem_setOf_eq] at ht
      obtain ⟨f, -, hf⟩ := ht
      exact ⟨f, hf⟩
    simp only [dif_pos h]
    exact h.choose_spec
  obtain ⟨S, hS⟩ := X.Γ_index
  let q := fun t (s : GL (Fin r) E) (k : Fin r) (i : Fin (finrank ℤ X.Λ)) =>
    (RealPlaceEmbeddings.qb X (rep t)).repr ((s : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single k 1) i
  set Q : ℝ := ∑ t ∈ hfin.toFinset, ∑ s ∈ S, ∑ k : Fin r, ∑ i : Fin (finrank ℤ X.Λ),
      ‖((q t s k i : ℚ) : ℂ)‖ with hQ_def
  have hG0 : (0:ℝ) ≤ ∑ τ : X.Ψ, ∑ k : Fin r, ∑ a : Fin r, ‖(X.Gm.map τ.1)⁻¹ k a‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      norm_nonneg _
  set G0 : ℝ := ∑ τ : X.Ψ, ∑ k : Fin r, ∑ a : Fin r, ‖(X.Gm.map τ.1)⁻¹ k a‖ with hG0_def
  refine ⟨CompactEntryBounds.Kset X (∑ _k : Fin r, G0 * (Q * (1 + B * HermitianPsiBounds.Cinv X))),
    CompactEntryBounds.Kset_compact (X := X) _, CompactEntryBounds.Kset_sub (X := X) _, ?_⟩
  intro x hx hl
  obtain ⟨b, hb, hnf⟩ := MajorantNormalForms.exists_normal_frame (X := X) hx
  have hy : IntegralBasisReduction.IsNormal X (mat (rmul x b)) := by
    unfold IntegralBasisReduction.IsNormal
    intro τ
    exact ⟨CompactEntryBounds.det_ne_of_gram (X := X) (hnf τ).1, (hnf τ).1⟩
  have hmin : ∀ v ∈ X.Λ, v ≠ 0 → ε ^ 2 ≤ QuadraticLatticeForms.Qy X (mat (rmul x b)) v := fun v hv hv0 =>
    HermitianPsiBounds.sq_le_Qy_of_le_firstMinimum (X := X) (x := x) (y := mat (rmul x b)) (fun τ u => (hnf τ).2 u) hε hl hv hv0
  obtain ⟨f, hfB, hfZ⟩ := IntegralBasisReduction.reduce (X := X) hy hm hmin

  have hmem : HermitianLatticeMaps.ty X f ∈ FiniteTranslateSets.TS X (ι := Fin (finrank ℤ X.Λ)) R T := by
    simp only [FiniteTranslateSets.TS, FiniteTranslateSets.Sh, FiniteTranslateSets.Sz, Set.mem_setOf_eq]
    refine ⟨f, ⟨fun i j => ?_, fun k i j => ?_⟩, rfl⟩
    · refine ⟨⟨(X.den : E) * herm X.Gm (f i : Fin r → E) (f j : Fin r → E),
        X.Λ_int _ (f i).2 _ (f j).2⟩, rfl, fun σ => ?_⟩
      show ‖σ ((X.den : E) * herm X.Gm (f i : Fin r → E) (f j : Fin r → E))‖ ≤ R
      rw [map_mul, norm_mul]
      have h1 : ‖σ (X.den : E)‖ ≤ D :=
        Finset.single_le_sum (f := fun σ : E →+* ℂ => ‖σ (X.den : E)‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ σ)
      have h2 := HermitianPsiBounds.herm_bound (X := X) hy σ (f i : Fin r → E) (f j : Fin r → E)
      have h3 : (QuadraticLatticeForms.Qy X (mat (rmul x b)) (f i : Fin r → E) +
          QuadraticLatticeForms.Qy X (mat (rmul x b)) (f j : Fin r → E)) * HermitianPsiBounds.Cinv X ≤
          (B + B) * HermitianPsiBounds.Cinv X :=
        mul_le_mul_of_nonneg_right (add_le_add (hfB i) (hfB j)) hC
      exact mul_le_mul h1 (h2.trans h3) (norm_nonneg _) hD
    · show (((f.repr (RingOfIntegers.basis E k • f i) j : ℤ) : ℝ)) ^ 2 ≤ T
      have h2 : QuadraticLatticeForms.Qy X (mat (rmul x b))
          ((RingOfIntegers.basis E k • f i : X.Λ) : Fin r → E) ≤ W * B := by
        rw [HermitianLatticeMaps.smul_coe (X := X)]
        refine (HermitianPsiBounds.Qy_smul (X := X) _ _ _).trans
          (mul_le_mul ?_ (hfB i) (QuadraticLatticeForms.Qy_nonneg (X := X) _ _) hW)
        exact Finset.single_le_sum (f := fun k : Free.ChooseBasisIndex ℤ (𝓞 E) =>
            ∑ τ : X.Ψ, ‖τ.1 ((RingOfIntegers.basis E k : 𝓞 E) : E)‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ k)
      calc _ ≤ _ := hfZ _ j
        _ ≤ 9 ^ (finrank ℤ X.Λ) * (W * B) / ε ^ 2 := by gcongr
  have hts : HermitianLatticeMaps.ty X (rep (HermitianLatticeMaps.ty X f)) = HermitianLatticeMaps.ty X f := hrep _ hmem
  obtain ⟨γ, hγU, -, hγinv⟩ :=
    HermitianLatticeMaps.exists_gl (X := X) (f := f) (f' := rep (HermitianLatticeMaps.ty X f)) hts.symm
  obtain ⟨s, hsS, hsΓ⟩ := hS γ hγU
  refine ⟨s⁻¹ * γ, hsΓ, b, hb, ?_⟩
  have hgU := X.Γ_stab _ hsΓ
  simp only [CompactEntryBounds.Kset, Set.mem_setOf_eq]
  intro τ
  have hgram : gram τ.1 X.Gm (((s⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      mat (rmul x b) τ) = diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) := by
    rw [CompactEntryBounds.gram_stab (X := X) hgU.1]
    exact (hnf τ).1
  refine ⟨hgram, fun a c => ?_⟩
  show ‖(((s⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
    mat (rmul x b) τ) a c‖ ≤ _
  have hdet := CompactEntryBounds.det_ne_of_gram (X := X) hgram
  refine (CompactEntryBounds.entry_bound (X := X) hdet hgram a c).trans (Finset.sum_le_sum fun k _ => ?_)
  refine mul_le_mul ?_ ?_ (norm_nonneg _) hG0
  · have e1 := Finset.single_le_sum (f := fun a' : Fin r => ‖(X.Gm.map τ.1)⁻¹ k a'‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
    have e2 := Finset.single_le_sum
      (f := fun k' : Fin r => ∑ a' : Fin r, ‖(X.Gm.map τ.1)⁻¹ k' a'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k)
    have e3 := Finset.single_le_sum
      (f := fun τ' : X.Ψ => ∑ k' : Fin r, ∑ a' : Fin r, ‖(X.Gm.map τ'.1)⁻¹ k' a'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ τ)
    exact e1.trans (e2.trans e3)
  · have hemb : Data.emb τ.1 (Pi.single k (1:E)) = Pi.single k 1 := by
      funext a'
      by_cases h : a' = k
      · subst h; simp [Data.emb]
      · simp [Data.emb, h]
    have hcol : ((((s⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
        mat (rmul x b) τ)⁻¹) c k =
        ((((s⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
        mat (rmul x b) τ)⁻¹ *ᵥ Data.emb τ.1 (Pi.single k 1)) c := by
      rw [hemb]
      first
        | (simp; done)
        | (simp [Matrix.mulVec, dotProduct, Pi.single_apply]; done)
        | (simp [Matrix.mulVec, Matrix.dotProduct, Pi.single_apply]; done)
    rw [hcol, CompactEntryBounds.inv_lact]
    have hginv : (((s⁻¹ * γ)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single k 1 =
        ∑ i, q (HermitianLatticeMaps.ty X f) s k i • (f i : Fin r → E) := by
      rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec]
      exact hγinv _
    rw [hginv]
    refine (CompactEntryBounds.comb_bound (X := X) (mat (rmul x b)) τ (q (HermitianLatticeMaps.ty X f) s k)
      (fun i => (f i : Fin r → E)) c).trans ?_
    have hterm : ∀ i, ‖((q (HermitianLatticeMaps.ty X f) s k i : ℚ) : ℂ)‖ *
        (1 + QuadraticLatticeForms.Qy X (mat (rmul x b)) (f i : Fin r → E) / X.c τ) ≤
        ‖((q (HermitianLatticeMaps.ty X f) s k i : ℚ) : ℂ)‖ * (1 + B * HermitianPsiBounds.Cinv X) := by
      intro i
      refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (norm_nonneg _)
      rw [div_eq_mul_one_div]
      exact mul_le_mul (hfB i) (HermitianPsiBounds.inv_c_le (X := X) τ)
        (le_of_lt (one_div_pos.mpr (QuadraticLatticeForms.c_pos (X := X) τ))) hB0
    refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (add_nonneg zero_le_one (mul_nonneg hB0 hC))
    have i1 := Finset.single_le_sum
      (f := fun k' : Fin r => ∑ i : Fin (finrank ℤ X.Λ), ‖((q (HermitianLatticeMaps.ty X f) s k' i : ℚ) : ℂ)‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k)
    have i2 := Finset.single_le_sum
      (f := fun s' : GL (Fin r) E => ∑ k' : Fin r, ∑ i : Fin (finrank ℤ X.Λ),
        ‖((q (HermitianLatticeMaps.ty X f) s' k' i : ℚ) : ℂ)‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hsS
    have i3 := Finset.single_le_sum
      (f := fun t' => ∑ s' ∈ S, ∑ k' : Fin r, ∑ i : Fin (finrank ℤ X.Λ),
        ‖((q t' s' k' i : ℚ) : ℂ)‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (hfin.mem_toFinset.mpr hmem)
    exact i1.trans (i2.trans i3)

end ReciprocityTheory.ChartRestriction.G.FD
end
end
