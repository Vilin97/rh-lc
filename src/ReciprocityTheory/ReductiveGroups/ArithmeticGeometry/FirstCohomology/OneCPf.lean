module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullbackValuationInvarianceOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ClosedPointWeilPower
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Topology.Sheaves.Presheaf

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.IntegralRingEmbedding

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding

open Module

variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))

lemma wt_zero_of_add {a b : WithTop ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 0) : a = 0 := by
  refine le_antisymm ?_ ha
  rw [← h]
  exact le_add_of_nonneg_right hb

lemma wt_inv_nonneg {a b : WithTop ℚ} (h : a + b = 0) (ha : a < 0) : 0 ≤ b := by
  have ha' : a ≠ ⊤ := ne_top_of_lt ha
  lift a to ℚ using ha'
  induction b using WithTop.recTopCoe with
  | top => exact le_top
  | coe q =>
    have h1 : (a : ℚ) + q = 0 := by exact_mod_cast h
    have h2 : (a : ℚ) < 0 := by exact_mod_cast ha
    exact_mod_cast (show (0 : ℚ) ≤ q by linarith)

def intRing : ValuationSubring F where
  carrier := {a | 0 ≤ v a}
  mul_mem' := fun {a b} ha hb => by
    show 0 ≤ v (a * b)
    rw [AddValuation.map_mul]; exact add_nonneg ha hb
  one_mem' := by show 0 ≤ v 1; rw [AddValuation.map_one]
  add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (AddValuation.map_add v a b)
  zero_mem' := by show 0 ≤ v 0; rw [AddValuation.map_zero]; exact le_top
  neg_mem' := fun {a} ha => by show 0 ≤ v (-a); rw [AddValuation.map_neg]; exact ha
  mem_or_inv_mem' := by
    intro a
    by_cases ha : 0 ≤ v a
    · exact Or.inl ha
    · right
      push Not at ha
      have ha0 : a ≠ 0 := by
        rintro rfl; rw [AddValuation.map_zero] at ha; exact absurd ha (not_lt.mpr le_top)
      show 0 ≤ v a⁻¹
      have : v a + v a⁻¹ = 0 := by
        rw [← AddValuation.map_mul, mul_inv_cancel₀ ha0, AddValuation.map_one]
      exact wt_inv_nonneg this ha

lemma mem_intRing {a : F} : a ∈ intRing v ↔ 0 ≤ v a := Iff.rfl

lemma isUnit_of_val_zero (x : intRing v) (hx : v (x : F) = 0) : IsUnit x := by
  have hx0 : (x : F) ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hx
    simp at hx
  have hinv : 0 ≤ v (x : F)⁻¹ := by
    have h1 : v (x : F) + v (x : F)⁻¹ = 0 := by
      rw [← AddValuation.map_mul, mul_inv_cancel₀ hx0, AddValuation.map_one]
    rw [hx, zero_add] at h1
    rw [h1]
  refine isUnit_iff_exists_inv.2 ⟨⟨(x : F)⁻¹, (mem_intRing v).2 hinv⟩, ?_⟩
  apply Subtype.ext
  exact mul_inv_cancel₀ hx0

lemma val_pos_of_mem_max (x : intRing v) (hx : x ∈ IsLocalRing.maximalIdeal (intRing v)) :
    0 < v (x : F) := by
  have hnu : ¬ IsUnit x := (IsLocalRing.mem_maximalIdeal x).1 hx
  have h0 : 0 ≤ v (x : F) := (mem_intRing v).1 x.2
  exact lt_of_le_of_ne h0 (fun h => hnu (isUnit_of_val_zero v x h.symm))

lemma val_root_unity {N : ℕ} (hN : 1 ≤ N) {z : F} (hz : z ^ N = 1) : v z = 0 := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hz
    exact zero_ne_one hz
  have h1 : v (z ^ N) = N • v z := AddValuation.map_pow v z N
  rw [hz, AddValuation.map_one] at h1
  have h2 : v z + v z⁻¹ = 0 := by
    rw [← AddValuation.map_mul, mul_inv_cancel₀ hz0, AddValuation.map_one]
  generalize v z = w at h1 h2 ⊢
  induction w using WithTop.recTopCoe with
  | top => simp at h2
  | coe q =>
    have h3 : ((N • q : ℚ) : WithTop ℚ) = 0 := by
      rw [WithTop.coe_nsmul]
      exact h1.symm
    have h4 : N • q = 0 := by exact_mod_cast h3
    rw [nsmul_eq_mul] at h4
    have h5 : q = 0 := (mul_eq_zero.1 h4).resolve_left (by exact_mod_cast (show N ≠ 0 by omega))
    simp [h5]

lemma val_sub_roots {N : ℕ} (hN : 1 ≤ N) (hvN : v (N : F) = 0) {z z' : F} (hz : z ^ N = 1)
    (hz' : z' ^ N = 1) (hne : z ≠ z') : v (z - z') = 0 := by
  have hvz := val_root_unity v hN hz
  have hvz' := val_root_unity v hN hz'
  have hnn : 0 ≤ v (z - z') :=
    le_trans (le_of_eq (by rw [hvz, hvz', min_self])) (AddValuation.map_sub v z z')
  by_contra hne0
  obtain ⟨Z, rfl⟩ : ∃ Z : intRing v, (Z : F) = z := ⟨⟨z, (mem_intRing v).2 (le_of_eq hvz.symm)⟩, rfl⟩
  obtain ⟨Z', rfl⟩ : ∃ Z' : intRing v, (Z' : F) = z' :=
    ⟨⟨z', (mem_intRing v).2 (le_of_eq hvz'.symm)⟩, rfl⟩
  have hZN : Z ^ N = 1 := Subtype.ext (by simpa using hz)
  have hZ'N : Z' ^ N = 1 := Subtype.ext (by simpa using hz')
  have hmax : Z - Z' ∈ IsLocalRing.maximalIdeal (intRing v) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h3 : ((Z : F) - Z') * (w : F) = 1 := by
      have := congrArg Subtype.val hw
      simpa using this
    have h1 : v ((Z : F) - Z') + v (w : F) = 0 := by
      rw [← AddValuation.map_mul, h3, AddValuation.map_one]
    exact hne0 (wt_zero_of_add hnn ((mem_intRing v).1 w.2) h1)
  have hres : IsLocalRing.residue (intRing v) Z = IsLocalRing.residue (intRing v) Z' := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hmax
  have hsum0 : ∑ i ∈ Finset.range N, Z ^ i * Z' ^ (N - 1 - i) = 0 := by
    have h1 := geom_sum₂_mul Z Z' N
    rw [hZN, hZ'N, sub_self] at h1
    have hne' : Z - Z' ≠ 0 := by
      intro h
      apply hne
      rw [sub_eq_zero] at h
      rw [h]
    exact (mul_eq_zero.1 h1).resolve_right hne'
  have hmap := congrArg (IsLocalRing.residue (intRing v)) hsum0

  rw [map_sum, map_zero] at hmap
  simp only [map_mul, map_pow, ← hres] at hmap
  rw [geom_sum₂_self] at hmap
  have hres0 : IsLocalRing.residue (intRing v) Z ≠ 0 :=
    ((isUnit_of_val_zero v Z hvz).map (IsLocalRing.residue (intRing v))).ne_zero
  have hN0 : ((N : ℕ) : IsLocalRing.ResidueField (intRing v)) = 0 :=
    (mul_eq_zero.1 hmap).resolve_right (pow_ne_zero _ hres0)
  rw [← map_natCast (IsLocalRing.residue (intRing v)) N, IsLocalRing.residue_eq_zero_iff] at hN0
  have hpos := val_pos_of_mem_max v (N : intRing v) hN0
  have hc : ((N : intRing v) : F) = (N : F) := by simp
  rw [hc, hvN] at hpos
  exact lt_irrefl _ hpos

section Core

variable {W : Type} [AddCommGroup W] [Module F W] {n : ℕ} (b : Fin n → W)

theorem span_of_eigen (UU Pos : W → Prop) (hb : LinearIndependent F b)
    (hUU : ∀ s, UU s ↔ ∃ c : Fin n → F, (∀ i, 0 ≤ v (c i)) ∧ s = ∑ i, c i • b i)
    (hPos : ∀ s, UU s → ∀ ζ : F, ∀ s', 0 < v ζ → UU s' → s = ζ • s' → Pos s)
    (hπ : ∃ π : F, 0 < v π)
    {ι Γ : Type} [Fintype ι] (hcard : Fintype.card ι = n) (sv : ι → W)
    (hsv : ∀ i, UU (sv i)) (hsvp : ∀ i, ¬ Pos (sv i))
    (T : Γ → W →ₗ[F] W) (hT : ∀ γ s, UU s → UU (T γ s))
    {N : ℕ} (hN : 1 ≤ N) (hvN : v (N : F) = 0) (χ : ι → Γ → F)
    (hχN : ∀ i γ, χ i γ ^ N = 1) (heig : ∀ i γ, T γ (sv i) = χ i γ • sv i)
    (hsep : ∀ i j, i ≠ j → ∃ γ, χ i γ ≠ χ j γ) :
    ∀ s, UU s → ∃ a : ι → F, (∀ i, 0 ≤ v (a i)) ∧ s = ∑ i, a i • sv i := by
  classical
  have hUU0 : UU 0 := (hUU 0).2 ⟨0, fun i => by simp, by simp⟩
  have hUUsub : ∀ s t, UU s → UU t → UU (s - t) := by
    intro s t hs ht
    obtain ⟨c, hc, rfl⟩ := (hUU s).1 hs
    obtain ⟨d, hd, rfl⟩ := (hUU _).1 ht
    refine (hUU _).2 ⟨c - d, fun i => ?_, ?_⟩
    · exact le_trans (le_min (hc i) (hd i)) (AddValuation.map_sub v (c i) (d i))
    · simp [sub_smul, Finset.sum_sub_distrib]
  have hUUsmul : ∀ r s, 0 ≤ v r → UU s → UU (r • s) := by
    intro r s hr hs
    obtain ⟨c, hc, rfl⟩ := (hUU s).1 hs
    refine (hUU _).2 ⟨fun i => r * c i, fun i => ?_, ?_⟩
    · show 0 ≤ v (r * c i)
      rw [AddValuation.map_mul]
      exact add_nonneg hr (hc i)
    · simp [Finset.smul_sum, mul_smul]
  have hsv0 : ∀ i, sv i ≠ 0 := by
    intro i h
    apply hsvp i
    exact hPos (sv i) (hsv i) 0 0 (by simp) hUU0 (by rw [h, zero_smul])
  have hχv : ∀ i γ, v (χ i γ) = 0 := fun i γ => val_root_unity v hN (hχN i γ)
  have hχd : ∀ i j γ, χ i γ ≠ χ j γ → v (χ i γ - χ j γ) = 0 :=
    fun i j γ h => val_sub_roots v hN hvN (hχN i γ) (hχN j γ) h

  have hred : ∀ (S : Finset ι) (a : ι → F) (j : ι) (γ : Γ), j ∈ S →
      T γ (∑ i ∈ S, a i • sv i) - χ j γ • ∑ i ∈ S, a i • sv i =
        ∑ i ∈ S.erase j, (a i * (χ i γ - χ j γ)) • sv i := by
    intro S a j γ hj

    rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    have hterm : ∀ i, T γ (a i • sv i) - χ j γ • (a i • sv i) = (a i * (χ i γ - χ j γ)) • sv i := by
      intro i
      rw [map_smul, heig, smul_smul, smul_smul, ← sub_smul]
      congr 1
      ring
    simp_rw [hterm]
    rw [← Finset.sum_erase_add _ _ hj, sub_self, mul_zero, zero_smul, add_zero]

  have indep : ∀ S : Finset ι, ∀ a : ι → F, ∑ i ∈ S, a i • sv i = 0 → ∀ k ∈ S, a k = 0 := by
    intro S
    induction S using Finset.strongInduction
    rename_i S ih
    intro a ha k hk
    by_cases hex : ∃ j ∈ S, j ≠ k
    · obtain ⟨j, hj, hjk⟩ := hex
      obtain ⟨γ, hγ⟩ := hsep k j (Ne.symm hjk)
      have hz : ∑ i ∈ S.erase j, (a i * (χ i γ - χ j γ)) • sv i = 0 := by
        rw [← hred S a j γ hj, ha, map_zero, smul_zero, sub_zero]
      have h1 : a k * (χ k γ - χ j γ) = 0 :=
        ih (S.erase j) (Finset.erase_ssubset hj) (fun i => a i * (χ i γ - χ j γ)) hz k
          (Finset.mem_erase.2 ⟨Ne.symm hjk, hk⟩)
      exact (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 hγ)
    · rw [Finset.sum_eq_single k (fun j hj hjk => absurd ⟨j, hj, hjk⟩ hex)
        (fun h => absurd hk h)] at ha
      exact (smul_eq_zero.1 ha).resolve_right (hsv0 k)

  have key : ∀ S : Finset ι, ∀ a : ι → F, UU (∑ i ∈ S, a i • sv i) → ∀ k ∈ S, 0 ≤ v (a k) := by
    intro S
    induction S using Finset.strongInduction
    rename_i S ih
    intro a ha k hk
    by_cases hex : ∃ j ∈ S, j ≠ k
    · obtain ⟨j, hj, hjk⟩ := hex
      obtain ⟨γ, hγ⟩ := hsep k j (Ne.symm hjk)
      have hmem : UU (∑ i ∈ S.erase j, (a i * (χ i γ - χ j γ)) • sv i) := by
        rw [← hred S a j γ hj]
        exact hUUsub _ _ (hT γ _ ha) (hUUsmul _ _ (le_of_eq (hχv j γ).symm) ha)
      have h1 : 0 ≤ v (a k * (χ k γ - χ j γ)) :=
        ih (S.erase j) (Finset.erase_ssubset hj) (fun i => a i * (χ i γ - χ j γ)) hmem k
          (Finset.mem_erase.2 ⟨Ne.symm hjk, hk⟩)
      rw [AddValuation.map_mul, hχd k j γ hγ, add_zero] at h1
      exact h1
    · rw [Finset.sum_eq_single k (fun j hj hjk => absurd ⟨j, hj, hjk⟩ hex)
        (fun h => absurd hk h)] at ha
      by_contra hneg
      have hneg' : v (a k) < 0 := not_le.1 hneg
      have hak : a k ≠ 0 := by
        intro h0
        rw [h0, AddValuation.map_zero] at hneg'
        exact absurd hneg' (not_lt.2 le_top)
      have hsum : v (a k) + v (a k)⁻¹ = 0 := by
        rw [← AddValuation.map_mul, mul_inv_cancel₀ hak, AddValuation.map_one]
      have hpos : 0 < v (a k)⁻¹ := by
        refine lt_of_le_of_ne (wt_inv_nonneg hsum hneg') ?_
        intro h0
        rw [← h0, add_zero] at hsum
        rw [hsum] at hneg'
        exact lt_irrefl _ hneg'
      exact hsvp k (hPos (sv k) (hsv k) (a k)⁻¹ (a k • sv k) hpos ha
        (by rw [smul_smul, inv_mul_cancel₀ hak, one_smul]))
  have hli : LinearIndependent F sv := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    exact indep Finset.univ g hg i (Finset.mem_univ i)
  have hmemb : ∀ s, UU s → s ∈ Submodule.span F (Set.range b) := by
    intro s hs
    obtain ⟨c, -, rfl⟩ := (hUU s).1 hs
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  haveI : FiniteDimensional F (Submodule.span F (Set.range b)) :=
    FiniteDimensional.span_of_finite F (Set.finite_range b)
  have hspan : Submodule.span F (Set.range sv) = Submodule.span F (Set.range b) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hmemb _ (hsv i)
    · rw [finrank_span_eq_card hli, finrank_span_eq_card hb, hcard, Fintype.card_fin]
  intro s hs
  have hs' : s ∈ Submodule.span F (Set.range sv) := by
    rw [hspan]
    exact hmemb s hs
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hs'
  refine ⟨a, fun i => key Finset.univ a ?_ i (Finset.mem_univ i), ha.symm⟩
  rw [ha]
  exact hs

end Core

end ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCPf

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem oneC_of_lemma {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (ζ : F) (s : Fam D F k) : Fam.IsSmul D F ζ s (ζ • s) := by
  intro α j
  rfl

private theorem oneC_of_lemma_2 {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (p : QkPt D F k) :
    ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)), w.IsGen :=
  ClosedPointWeilPower.gen_local_linComb (V := F) D.P.L D.P.isLB _ _

private theorem oneC_of_lemma_3 (F : Type) [Field F] (c : (Γ(Sp F, ⊤))ˣ) : ∃ z : Fˣ, unitOn z = c :=
  ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom c, by
    ext
    simp [unitOn]⟩

private theorem oneC_of_lemma_4 {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (s s' : Fam D F k)
    (h : ∀ α j, (s.s α).f j = (s'.s α).f j) : s = s' := by
  obtain ⟨s, hs⟩ := s
  obtain ⟨s', hs'⟩ := s'
  have key : ∀ α, s α = s' α := by
    intro α
    have hab : (s α).f = (s' α).f := funext (h α)
    revert hab
    generalize s α = a
    generalize s' α = b
    cases a
    cases b
    intro hab
    cases hab
    rfl
  have e : s = s' := funext key
  subst e
  rfl

private theorem oneC_of_lemma_5 {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (ζ : F) (s s' : Fam D F k) (h : Fam.IsSmul D F ζ s s') :
    s' = ζ • s :=
  oneC_of_lemma_4 D F k s' (ζ • s) fun α j => (h α j).trans (oneC_of_lemma D F k ζ s α j).symm

private theorem oneC_of_lemma_6 (F : Type) [Field F] (z : Fˣ) (n : ℕ) (h : unitOn z ^ n = 1) :
    (z : F) ^ n = 1 := by
  have key : ∀ u : Fˣ,
      Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom (unitOn u) = u := by
    intro u
    ext
    simp [unitOn]
  have e := congrArg (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom) h
  rw [map_pow, key, map_one] at e
  simpa using congrArg Units.val e

theorem oneC_of (hL : Laws) (hΦ : PhiFunStatement) (h1c : PositiveValuationMaximalIdeal) (h2 : PullbackValuationForwardBound)
    (h2f : DvrLevelFrame) (h3 : FiniteOrderValuationInvariance) (hU : UUStatement) (hE : FinOrdExistsStatement) (hB : AlphaBarEnumStatement)
    (hC : CanonLiftFixStatement) (hD : AlphaPairStatement) (hdim : DimSplitStatement) :
    OneCStatement := by
  intro E _ _ _ H V _ _ _ t P hT α N hN hαN hcop hNu ϖ hϖ Q hQ F _ _ _ v hv Dw I θ hθ hprim θα hpull s hs
  letI := H.starRing
  have hk : 1 ≤ 1 * N := by omega
  have hαN' : star α * α = (N : 𝓞 E) := by rw [_root_.mul_comm]; exact hαN

  have htor : ∀ (a b : 𝓞 E) (y : TFK (R := V) F ⟶ P.A.A), a * b = (N : 𝓞 E) →
      y ≫ P.oA.act b = 1 → y ^ (1 * N) = 1 := by
    intro a b y hab hy
    rw [_root_.one_mul, ← ClosedPointWeilPower.comp_act_nat P.oA.toRingAct y N hN, ← hab, P.oA.map_mul,
      ← Category.assoc, hy]
    exact ClosedPointWeilPower.one_comp_hom _ (P.oA.hom a)

  obtain ⟨p, x, hpx, hxα, hinj, -⟩ := hB E H V t P hT α N hN hαN hcop hNu F Dw I
  have hcop' : ∃ u u' : 𝓞 E, u * star α + u' * star (star α) = 1 := by
    obtain ⟨u, u', h⟩ := hcop
    exact ⟨u', u, by rw [star_star, _root_.add_comm]; exact h⟩
  obtain ⟨p', x', hpx', hxα', -, hsurj'⟩ :=
    hB E H V t P hT (star α) N hN (by rw [star_star]; exact hαN') hcop' hNu F Dw I
  have hxa : ∀ gm, x' gm ≫ P.oA.act α = 1 := fun gm => by simpa only [star_star] using hxα' gm
  obtain ⟨f, hfToA, -, -, -, -, hfW⟩ := hT F (1 * N) hk
  have hfp : ∀ i, x i = f (p i) := fun i => (hfToA (p i) (x i)).mp (hpx i)
  have hfq : ∀ gm, x' gm = f (p' gm) := fun gm => (hfToA (p' gm) (x' gm)).mp (hpx' gm)
  have htx : ∀ i, x i ^ (1 * N) = 1 := fun i => htor α (star α) (x i) hαN (hxα i)
  have htx' : ∀ gm, x' gm ^ (1 * N) = 1 := fun gm => htor (star α) α (x' gm) hαN' (hxa gm)

  have hw : ∀ b, ∃ w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p b).g.b)
      (DegPre.lineε (1 * N))), w.IsGen := fun b => oneC_of_lemma_2 P.D.toPre F (1 * N) (p b)
  choose w hwg using hw
  have hz : ∀ b, ∃ ζ : F, ζ ≠ 0 ∧ FinOrd P.D F (1 * N) (p b) (w b) ζ :=
    fun b => hE V P.D F (1 * N) hk (p b) (w b) (hwg b)
  choose ζ hζ0 hfin using hz
  choose Φ hΦb using fun b => hΦ V (maximalIdeal V) P.D F (1 * N) hk (p b) (w b) (hwg b)
  choose wq hwqg hwq1 hfix using fun gm =>
    hC E H V t P hT α N hN hαN hcop hNu F θ θα hpull (p' gm) (x' gm) (hpx' gm) (hxa gm)
  choose Φq hΦq using fun gm => hΦ V (maximalIdeal V) P.D F (1 * N) hk (p' gm) (wq gm) (hwqg gm)

  have hWex : ∀ i gm, ∃ z : Fˣ, WeilIs P.A.A P.A.L ((1 * N : ℕ) : ℤ) (x' gm) (x i) (unitOn z) := by
    intro i gm
    obtain ⟨c, hc, -⟩ := (hL.weil _ P.A (1 * N) _).1 (x' gm) (x i) (htx' gm) (htx i)
    obtain ⟨z, rfl⟩ := oneC_of_lemma_3 F c
    exact ⟨z, hc⟩
  choose χz hχz using hWex
  have hEig : ∀ i gm, Φq gm (Φ i θα) = (χz i gm : F) • Φ i θα := by
    intro i gm
    apply oneC_of_lemma_5
    have hW' : WeilQkIs P.D.toPre F (1 * N) (p' gm) (p i) (χz i gm) :=
      (hfW (p' gm) (p i) (χz i gm)).mpr (by rw [← hfq gm, ← hfp i]; exact hχz i gm)
    exact hW' (wq gm) (w i) (hwqg gm) (hwg i) θα (Φ i θα) (Φq gm (Φ i θα)) θα (Φ i θα)
      ((hΦb i θα _).mpr rfl) ((hΦq gm (Φ i θα) _).mpr rfl) (hfix gm) ((hΦb i θα _).mpr rfl)

  have hvN : v (((1 * N : ℕ)) : F) = 0 := by
    have h := hv ((N : ℕ) : FractionRing V) 0 ⟨hNu.unit, by simp⟩
    simpa using h
  have hπ : ∃ π : F, 0 < v π := by
    refine ⟨algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ), ?_⟩
    rw [hv _ 1 ⟨1, by simp⟩]
    exact_mod_cast (show (0 : ℚ) < ((1 : ℤ) : ℚ) by norm_num)

  have hθα0 : NuGe P.D Q F v (1 * N) θα 0 :=
    h2 V ϖ hϖ P.D Q hQ F v hv (𝓞 E) P.oD H.w0 P.w0 α N hN hαN hαN' 1 le_rfl θ θα hpull 0 hθ
  have hsm1 : ∀ {k : ℕ} (u : Fam P.D.toPre F k), Fam.IsSmul P.D.toPre F 1 u u := by
    intro k u
    have h := oneC_of_lemma P.D.toPre F k 1 u
    rwa [one_smul] at h
  have hnotpos : ∀ r : ℚ, 0 < r → ¬ NuGe P.D Q F v (1 * N) θα r := by
    intro r hr h
    obtain ⟨σ, σF, hscal, hσ, hnd⟩ := hprim
    have hb := h2f V ϖ hϖ P.D Q hQ F v hv (𝓞 E) P.oD H.w0 P.w0 α N hN hαN 1 le_rfl θ θα hpull 0
      σ σF 1 hscal (fun j => by rw [← hσ j]; exact hsm1 θ 0 j) hnd r h
    rw [AddValuation.map_one, QForm.Q_zero hϖ P.D hQ] at hb
    have h' : ((r : ℚ) : WithTop ℚ) ≤ ((0 : ℚ) : WithTop ℚ) := by simpa using hb
    have := WithTop.coe_le_coe.mp h'
    linarith
  have hN3 : ∀ i r, NuGe P.D Q F v (1 * N) θα r ↔ NuGe P.D Q F v (1 * N) (ζ i • Φ i θα) r :=
    fun i r => h3 V ϖ hϖ P.D Q hQ F v hv (1 * N) hk (p i) (w i) (hwg i) (ζ i) (hζ0 i) (hfin i)
      θα (Φ i θα) (ζ i • Φ i θα) ((hΦb i θα _).mpr rfl) (oneC_of_lemma _ _ _ _ _) r

  obtain ⟨bb, hbli, -, hbspan⟩ := hU V ϖ hϖ P.D Q hQ F v hv (Or.inl inferInstance) (1 * N) hk
  have hcard : Fintype.card (Fin (N ^ P.A.g)) = (1 * N) ^ (P.D.toPre.rank + P.D.toPre.P.g) := by
    rw [Fintype.card_fin, hdim E H V t P, _root_.one_mul]
  obtain ⟨a, ha0, hsa⟩ := IntegralRingEmbedding.span_of_eigen (F := F) (v := v) (b := bb) (n := _)
    (fun u => NuGe P.D Q F v (1 * N) u 0) (fun u => ∃ r : ℚ, 0 < r ∧ NuGe P.D Q F v (1 * N) u r)
    hbli hbspan
    (fun s0 hs0 ζ0 s' hζ hs' he => (h1c V ϖ hϖ P.D Q hQ F v hv (1 * N) hk s0 hs0).mpr
      ⟨ζ0, s', hζ, hs', by rw [he]; exact oneC_of_lemma _ _ _ ζ0 s'⟩)
    hπ hcard (fun i => ζ i • Φ i θα) (fun i => (hN3 i 0).mp hθα0)
    (fun i hp => by
      obtain ⟨r, hr, hr'⟩ := hp
      exact hnotpos r hr ((hN3 i r).mpr hr'))
    Φq
    (fun gm s0 hs0 => (h3 V ϖ hϖ P.D Q hQ F v hv (1 * N) hk (p' gm) (wq gm) (hwqg gm) 1 one_ne_zero
      (hwq1 gm) s0 (Φq gm s0) (Φq gm s0) ((hΦq gm s0 _).mpr rfl) (hsm1 _) 0).mp hs0)
    hk hvN (fun i gm => (χz i gm : F))
    (fun i gm => oneC_of_lemma_6 F (χz i gm) (1 * N)
      (ClosedPointWeilPower.weil_pow_eq_one hL.weil P.A (1 * N) (x' gm) (x i) (htx' gm) (htx i) _ (hχz i gm)))
    (fun i gm => by
      show Φq gm (ζ i • Φ i θα) = (χz i gm : F) • (ζ i • Φ i θα)
      rw [map_smul, hEig i gm, smul_comm])
    (fun i j hij => by
      obtain ⟨z, hz, c, c', hc, hc', hne⟩ := hD E H V t P hT α N hN hαN hcop hNu F Dw I (x i) (x j)
        (hxα i) (hxα j) (fun h => hij (hinj h))
      obtain ⟨gm, rfl⟩ := hsurj' z (by rw [star_star]; exact hz)
      refine ⟨gm, fun heq => hne ?_⟩
      have hc1 : WeilIs P.A.A P.A.L ((1 * N : ℕ) : ℤ) (x' gm) (x i) c := by rw [_root_.one_mul]; exact hc
      have hc1' : WeilIs P.A.A P.A.L ((1 * N : ℕ) : ℤ) (x' gm) (x j) c' := by
        rw [_root_.one_mul]; exact hc'
      rw [ClosedPointWeilPower.weil_unique hL.weil P.A (1 * N) (x' gm) (x i) (htx' gm) (htx i) _ _ hc1 (hχz i gm),
        ClosedPointWeilPower.weil_unique hL.weil P.A (1 * N) (x' gm) (x j) (htx' gm) (htx j) _ _ hc1' (hχz j gm),
        Units.ext heq])
    s hs
  exact ⟨N ^ P.A.g, p, x, w, ζ, fun i => ζ i • Φ i θα, a, hpx, hxα, fun i => ⟨hwg i, hζ0 i, hfin i⟩,
    fun i => ⟨Φ i θα, (hΦb i θα _).mpr rfl, oneC_of_lemma _ _ _ _ _⟩, ha0, hsa⟩

end ReciprocityTheory.ChartRestriction.G.H1
end
end
end
