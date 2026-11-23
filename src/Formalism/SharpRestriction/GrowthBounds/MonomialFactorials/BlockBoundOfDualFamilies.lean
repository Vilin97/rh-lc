module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundUniformiser
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.MemIntPolIff
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.PadicIntegersEmbeddingMapPrime
public import Formalism.SharpRestriction.GrowthBounds.ObjSeg
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ValuationNonnegIffIntegral
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Sheaves.Presheaf

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.StructureSheafH1BaseChange

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory

section Dual

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ}
  {V : Type} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem vLE_ne_zero' {κ : KK O} {D : ℝ} (h : vLE p κ D) : κ ≠ 0 := by
  rintro rfl
  obtain ⟨q, hq, -⟩ := h
  rw [valuation_zero_alt] at hq
  exact WithTop.top_ne_coe hq

theorem nv_irr' {w : O} (hw : Irreducible w) : dvrOrderNat w = 1 := by
  simp [dvrOrderNat, IsDiscreteValuationRing.addVal_uniformizer hw]

theorem vK_int_form (x : KK O) (hx : x ≠ 0) : ∃ k : ℤ, vK p x = (((k : ℚ) / (ramE p O : ℚ) : ℚ) : WithTop ℚ) := by
  unfold vK ordW
  rw [if_neg hx]
  exact ⟨_, rfl⟩

theorem vK_le_zero_of_not_int (S : UniformizedDVR p O) (a : KK O)
    (h : ¬ (0 : WithTop ℚ) ≤ vK p (a * (algebraMap O (KK O) S.w)⁻¹)) :
    ∃ q : ℚ, vK p a = (q : WithTop ℚ) ∧ q ≤ 0 := by
  have hw0 : S.w ≠ 0 := S.w_irr.ne_zero
  have hw0' : algebraMap O (KK O) S.w ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 hw0
  have hepos : (0 : ℚ) < ramE p O := by
    have := ramification_index_ne_zero S
    exact_mod_cast Nat.pos_of_ne_zero this
  have ha : a ≠ 0 := by
    rintro rfl
    apply h
    rw [zero_mul, valuation_zero_alt]
    exact le_top
  obtain ⟨k, hk⟩ := vK_int_form a ha
  have hwinv : vK p ((algebraMap O (KK O) S.w)⁻¹) =
      (((-1 : ℚ) / (ramE p O : ℚ) : ℚ) : WithTop ℚ) := by
    rw [valuation_eq_of_fraction p _ 1 S.w one_ne_zero hw0 (by rw [inv_mul_cancel₀ hw0', map_one]),
      nv_irr' S.w_irr]
    simp [dvrOrderNat]
  rw [valuation_mul_alt, hk, hwinv, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe] at h
  push_neg at h
  refine ⟨(k : ℚ) / (ramE p O : ℚ), hk, ?_⟩
  have h2 : ((k : ℚ) - 1) / (ramE p O : ℚ) < 0 := by
    rw [sub_div]
    rw [neg_div] at h
    linarith
  have h3 : (k : ℚ) - 1 < 0 := by
    by_contra hc
    push_neg at hc
    exact absurd h2 (not_lt.2 (div_nonneg hc hepos.le))
  have h4 : k < 1 := by exact_mod_cast (by linarith : (k : ℚ) < 1)
  have h5 : (k : ℚ) ≤ 0 := by exact_mod_cast (by omega : k ≤ 0)
  exact div_nonpos_of_nonpos_of_nonneg h5 hepos.le

theorem be_sum_left (be : V → V → KK O) (hsm : ∀ (a : KK O) (u v : V), be (a • u) v = a * be u v)
    (hadd : ∀ u u' v, be (u + u') v = be u v + be u' v) {n : ℕ} (a : Fin n → KK O) (x : Fin n → V) (v : V) :
    be (∑ i, a i • x i) v = ∑ i, a i * be (x i) v := by
  classical
  have h0 : be 0 v = 0 := by
    have := hsm 0 0 v
    rwa [zero_smul, zero_mul] at this
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp [h0]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd, hsm, ih]

theorem goodSub_of_dual (S : UniformizedDVR p O) (be : V → V → KK O)
    (hsm : ∀ (a : KK O) (u v : V), be (a • u) v = a * be u v)
    (hadd : ∀ u u' v, be (u + u') v = be u v + be u' v)
    (L : Submodule O V) {n : ℕ} (x y : Fin n → V) (hx : ∀ i, x i ∈ L) (hy : ∀ i, y i ∈ L)
    (c : KK O) (hxy : ∀ i j, be (x i) (y j) = if i = j then c else 0) (D : ℝ) (hc : vLE p c D) :
    ∃ L₂ : Submodule O V, GoodSub p be L L₂ D ∧ n ≤ Module.finrank O L₂ := by
  classical
  have hc0 : c ≠ 0 := vLE_ne_zero' hc
  have hw0 : S.w ≠ 0 := S.w_irr.ne_zero
  have hw0' : algebraMap O (KK O) S.w ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 hw0
  have hbe0 : ∀ v, be 0 v = 0 := fun v => by
    have := hsm 0 0 v
    rwa [zero_smul, zero_mul] at this
  have hsum : ∀ (t : Fin n → KK O) (j : Fin n), be (∑ i, t i • x i) (y j) = t j * c := by
    intro t j
    rw [be_sum_left be hsm hadd t x (y j)]
    simp [hxy]
  have hspan : ∀ s : Fin n → O,
      (∑ i, s i • x i) ∈ (Submodule.span (KK O) (Set.range x)).restrictScalars O := by
    intro s
    rw [Submodule.restrictScalars_mem]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← algebraMap_smul (KK O) (s i) (x i)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O, ⟨⟨inf_le_left, ?_⟩, ?_⟩, ?_⟩
  · intro o u ho hu hou
    refine Submodule.mem_inf.2 ⟨hu, ?_⟩
    have h2 := (Submodule.mem_inf.1 hou).2
    rw [Submodule.restrictScalars_mem] at h2 ⊢
    have ho' : algebraMap O (KK O) o ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 ho
    have hu' : u = (algebraMap O (KK O) o)⁻¹ • (o • u) := by
      rw [← algebraMap_smul (KK O) o u, smul_smul, inv_mul_cancel₀ ho', one_smul]
    rw [hu']
    exact Submodule.smul_mem _ _ h2
  · rintro u ⟨hu, hprim⟩
    obtain ⟨hul, huw⟩ := Submodule.mem_inf.1 hu
    rw [Submodule.restrictScalars_mem, Submodule.mem_span_range_iff_exists_fun] at huw
    obtain ⟨t, rfl⟩ := huw
    by_cases hall : ∀ j, 0 ≤ vK p (t j * (algebraMap O (KK O) S.w)⁻¹)
    · exfalso
      choose s hs using fun j => (valuation_nonneg_iff_integral S _).1 (hall j)
      have ht : ∀ j, t j = algebraMap O (KK O) S.w * algebraMap O (KK O) (s j) := by
        intro j
        rw [← hs j, mul_comm (t j), ← mul_assoc, mul_inv_cancel₀ hw0', one_mul]
      have hx' : (∑ i, s i • x i) ∈ L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O :=
        Submodule.mem_inf.2 ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hx i), hspan s⟩
      have hu' : (∑ i, t i • x i) = S.w • ∑ i, s i • x i := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [ht i, mul_smul, algebraMap_smul, algebraMap_smul]
      exact S.w_irr.not_isUnit (hprim S.w _ hx' hu')
    · push_neg at hall
      obtain ⟨j, hj⟩ := hall
      obtain ⟨q, hq, hq0⟩ := vK_le_zero_of_not_int S (t j) (not_le.2 hj)
      obtain ⟨qc, hqc, hqcD⟩ := hc
      have hq0' : (q : ℝ) ≤ 0 := by exact_mod_cast hq0
      refine ⟨y j, hy j, q + qc, ?_, ?_⟩
      · rw [hsum, valuation_mul_alt, hq, hqc, ← WithTop.coe_add]
      · push_cast
        linarith
  · have hli : LinearIndependent (KK O) x := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have := hsum g i
      rw [hg, hbe0] at this
      exact (mul_eq_zero.1 this.symm).resolve_right hc0
    have hliO : LinearIndependent O x := (LinearIndependent.iff_fractionRing O (KK O)).2 hli
    let f : Fin n → (L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O : Submodule O V) :=
      fun i => ⟨x i, Submodule.mem_inf.2 ⟨hx i, by
        rw [Submodule.restrictScalars_mem]
        exact Submodule.subset_span ⟨i, rfl⟩⟩⟩
    have hf : LinearIndependent O f :=
      LinearIndependent.of_comp (L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O).subtype hliO
    let φ : (L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O : Submodule O V) →ₗ[O]
        (Fin n → KK O) :=
      { toFun := fun u j => be u (y j)
        map_add' := fun u u' => by
          funext j
          exact hadd _ _ _
        map_smul' := fun o u => by
          funext j
          simp only [Submodule.coe_smul, RingHom.id_apply, Pi.smul_apply]
          rw [← algebraMap_smul (KK O) o (u : V), hsm, Algebra.smul_def] }
    have hφ : Function.Injective φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro u hu
      obtain ⟨-, huw⟩ := Submodule.mem_inf.1 u.2
      rw [Submodule.restrictScalars_mem, Submodule.mem_span_range_iff_exists_fun] at huw
      obtain ⟨t, ht⟩ := huw
      have ht0 : ∀ j, t j = 0 := fun j => by
        have h1 := congrFun hu j
        have h2 := hsum t j
        rw [ht] at h2
        change be (u : V) (y j) = 0 at h1
        rw [h1] at h2
        exact (mul_eq_zero.1 h2.symm).resolve_right hc0
      ext
      rw [← ht]
      simp [ht0]
    have hup : Module.rank O (L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O :
        Submodule O V) ≤ n := by
      calc Module.rank O (L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O :
            Submodule O V)
          ≤ Module.rank O (Fin n → KK O) := LinearMap.rank_le_of_injective φ hφ
        _ = Module.rank (KK O) (Fin n → KK O) :=
          (IsFractionRing.rank_right_eq (R := O) (S := KK O) (N := Fin n → KK O)).symm
        _ = n := by simp
    have hlow : (n : Cardinal) ≤ Module.rank O
        (L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O : Submodule O V) := by
      simpa using hf.cardinal_le_rank
    rw [Module.finrank_eq_of_rank_eq (le_antisymm hup hlow)]

end Dual

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundOfDualFamilies

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

section Val

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ}

theorem vK_one (p : ℕ) : vK p (1 : KK O) = 0 := by
  have h := valuation_algebraMap_eq_alt (O := O) p 1 one_ne_zero
  rw [map_one] at h
  rw [h, dvr_order_unit_eq_zero isUnit_one]
  simp

theorem vK_npow {x : KK O} {q : ℚ} (hx : vK p x = (q : WithTop ℚ)) (n : ℕ) :
    vK p (x ^ n) = (((n : ℚ) * q : ℚ) : WithTop ℚ) := by
  induction n with
  | zero => rw [pow_zero, vK_one]; simp
  | succ n ih =>
    rw [pow_succ, valuation_mul_alt, ih, hx, ← WithTop.coe_add]
    congr 1
    push_cast
    ring

theorem vK_inv' {x : KK O} (hx0 : x ≠ 0) {q : ℚ} (hx : vK p x = (q : WithTop ℚ)) :
    vK p x⁻¹ = ((-q : ℚ) : WithTop ℚ) := by
  have h := valuation_mul_alt (O := O) p x x⁻¹
  rw [mul_inv_cancel₀ hx0, vK_one, hx] at h
  cases ht : vK p x⁻¹ with
  | top => rw [ht] at h; simp at h
  | coe t =>
    rw [ht, ← WithTop.coe_add] at h
    have : q + t = 0 := by exact_mod_cast h.symm
    congr 1
    linarith

theorem vK_zpow {x : KK O} (hx0 : x ≠ 0) {q : ℚ} (hx : vK p x = (q : WithTop ℚ)) (k : ℤ) :
    vK p (x ^ k) = (((k : ℚ) * q : ℚ) : WithTop ℚ) := by
  cases k with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, vK_npow hx]; push_cast; rfl
  | negSucc n =>
    rw [zpow_negSucc, vK_inv' (pow_ne_zero _ hx0) (vK_npow hx (n + 1))]
    congr 1
    push_cast
    ring

end Val

section FockMap

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem fock_map (ι : ℚ_[p] →+* KK O) {σ : Type} (F G : MvPolynomial σ ℚ_[p]) :
    fock (map ι F) (map ι G) = ι (Formalism.GM.M.fockK F G) := by
  classical
  unfold fock Formalism.GM.M.fockK

  rw [support_map_of_injective _ ι.injective, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_map, coeff_map, map_mul, map_mul]
  congr 1
  unfold expFact
  simp only [Finsupp.prod, Nat.cast_prod, map_prod, map_natCast]

theorem fock_smul_both {σ : Type} (a : KK O) (A B : MvPolynomial σ (KK O)) :
    fock (a • A) (a • B) = a * (a * fock A B) := by
  rw [fock_form_smul_right, fock_form_symm, fock_form_smul_right, fock_form_symm B A, smul_eq_mul, smul_eq_mul]

end FockMap

section Assemble

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

theorem specConst_ne_zero {s r : ℕ} (p : ℕ) (S : SegData s) (b : SegBlock s r) : specConst p S b ≠ 0 := by
  unfold specConst
  rw [Finset.prod_ne_zero_iff]
  intro i _
  split_ifs
  · exact mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  · exact one_ne_zero

theorem ramE_eq_two : ramE X.p X.O = 2 := by
  have h2 : X.setting.w ^ 2 = (X.p : X.O) := Formalism.MainNotions.G.dvrOfStd_sq X.std
  have : ramE X.p X.O = dvrOrderNat (X.p : X.O) := rfl
  rw [this, ← h2, dvr_order_pow X.setting.w_irr.ne_zero, nv_irr' X.setting.w_irr]

theorem vK_w : vK X.p (algebraMap X.O (KK X.O) X.setting.w) = (((1 : ℚ) / 2 : ℚ) : WithTop ℚ) := by
  rw [valuation_algebraMap_eq_alt X.p _ X.setting.w_irr.ne_zero, nv_irr' X.setting.w_irr, ramE_eq_two]
  simp

theorem vK_p : vK X.p ((X.p : ℕ) : KK X.O) = ((1 : ℚ) : WithTop ℚ) := by
  rw [valuation_natCast_padicVal X.std.1.prime X.setting X.p X.std.1.prime.ne_zero, Nat.padicValNat_def, Nat.Prime.multiplicity_self]
  simp

theorem coeff_of_int {p : ℕ} [Fact p.Prime] {σ : Type} (F : MvPolynomial σ ℚ_[p]) (hF : F ∈ Formalism.GM.M.IntPol p σ)
    (v : σ →₀ ℕ) : ∃ c : ℤ_[p], F.coeff v = (c : ℚ_[p]) := by
  obtain ⟨F0, rfl⟩ := hF
  refine ⟨F0.coeff v, ?_⟩
  simp [MvPolynomial.coeff_map]

theorem block_dual_family_bound (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r) (D : ℤ) (n : ℕ)
    (x y : Fin n → MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) ℚ_[X.p]) (e : ℤ)
    (hx : ∀ i, x i ∈ (gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r))
    (hy : ∀ i, y i ∈ (gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r))
    (hxy : ∀ i j, Formalism.GM.M.fockK (x i) (y j) = if i = j then (X.p : ℚ_[X.p]) ^ e else 0)
    (hmon : ∀ z : MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) ℚ_[X.p],
      z ∈ (gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r) → ∀ μ ∈ z.support,
        (e : ℝ) ≤ (padicValNat X.p (μ.prod fun _ k => k.factorial) : ℝ) + D + levelPassageLoss X) :
    ∃ L₂ : Submodule X.O (MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) (KK X.O)),
      GoodSub X.p (blockForm X.O X.p X.r (X.S C0 CE1 CE2) b)
        (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b) L₂ ((D : ℝ) + levelPassageLoss X) ∧
      n ≤ Module.finrank X.O L₂ := by
  have hint := iotaX_int X
  set ι := iotaX X with hι
  set sp := specConst X.p (X.S C0 CE1 CE2) b with hsp
  set F : ℤ := ⌊(D : ℝ) + levelPassageLoss X⌋ with hF
  set k : ℤ := F - e - (padicValNat X.p sp : ℤ) with hk'
  set wK : KK X.O := algebraMap X.O (KK X.O) X.setting.w with hwK
  have hw0 : wK ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective X.O (KK X.O))).2 X.setting.w_irr.ne_zero
  set lam : KK X.O := wK ^ k with hlam
  have hvlam : vK X.p lam = ((((k : ℚ) * (1 / 2)) : ℚ) : WithTop ℚ) := vK_zpow hw0 (vK_w X) k

  have hmemL : ∀ z : MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) ℚ_[X.p],
      z ∈ (gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r) →
      lam • map ι z ∈ blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b := by
    intro z hz
    refine ⟨?_, ?_⟩
    · show lam • map ι z ∈ Submodule.span (KK X.O) _
      exact Submodule.smul_mem _ _ (map_SSZ hint (blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b) z hz)
    · have hzi : z ∈ Formalism.GM.M.IntPol X.p (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) :=
        SSZ_int (gB C0 CE1 CE2 X aTop aPlus b) z hz
      rw [MvPolynomial.as_sum (lam • map ι z)]
      refine Submodule.sum_mem _ fun v hv => Submodule.subset_span ⟨v, _, ?_, rfl⟩
      have hcv : (lam • map ι z).coeff v = lam * ι (z.coeff v) := by
        rw [MvPolynomial.coeff_smul, coeff_map, smul_eq_mul]
      have hzv : z.coeff v ≠ 0 := by
        intro h0
        rw [MvPolynomial.mem_support_iff, hcv, h0, map_zero, mul_zero] at hv
        exact hv rfl
      have hvz : v ∈ z.support := MvPolynomial.mem_support_iff.2 hzv
      have hm := hmon z hz v hvz
      obtain ⟨c0, hc0⟩ := coeff_of_int z hzi v
      obtain ⟨o, ho⟩ := hint c0
      have hcz : ι (z.coeff v) = algebraMap X.O (KK X.O) o := by rw [hc0]; exact ho
      have ho0 : (0 : WithTop ℚ) ≤ vK X.p (algebraMap X.O (KK X.O) o) :=
        (valuation_nonneg_iff_integral X.setting _).2 ⟨o, rfl⟩
      rw [hcv, valuation_mul_alt, hvlam, hcz]
      have hint2 : (0 : ℤ) ≤ k + (padicValNat X.p (expFact v) : ℤ) + (padicValNat X.p sp : ℤ) := by
        have h1 : e - (padicValNat X.p (expFact v) : ℤ) ≤ F := by
          rw [hF]
          apply Int.le_floor.2
          simp only [Int.cast_sub, Int.cast_natCast]
          have : (e : ℝ) ≤ (padicValNat X.p (expFact v) : ℝ) + D + levelPassageLoss X := hm
          linarith
        rw [hk']
        omega
      cases hvo : vK X.p (algebraMap X.O (KK X.O) o) with
      | top => simp
      | coe t =>
        rw [hvo] at ho0
        have ht : (0 : ℚ) ≤ t := by exact_mod_cast ho0
        rw [← WithTop.coe_add, ← WithTop.coe_add]
        have hq : (0 : ℚ) ≤ (k : ℚ) + (padicValNat X.p (expFact v) : ℚ) + (padicValNat X.p sp : ℚ) := by
          have h5 := (Int.cast_le (R := ℚ)).2 hint2
          simpa only [Int.cast_add, Int.cast_zero, Int.cast_natCast] using h5
        exact_mod_cast (show (0 : ℚ) ≤ (k : ℚ) * (1 / 2) + t +
          ((padicValNat X.p (expFact v) : ℚ) / 2 + (padicValNat X.p sp : ℚ) / 2) by linarith)

  set c : KK X.O := (sp : KK X.O) * (lam * (lam * ι ((X.p : ℚ_[X.p]) ^ e))) with hc
  have hform : ∀ i j, blockForm X.O X.p X.r (X.S C0 CE1 CE2) b (lam • map ι (x i)) (lam • map ι (y j)) = if i = j then c else 0 := by
    intro i j
    unfold blockForm
    rw [fock_smul_both, fock_map, hxy]
    split_ifs
    · rfl
    · simp
  have hvc : vLE X.p c ((D : ℝ) + levelPassageLoss X) := by
    have hsp0 : sp ≠ 0 := specConst_ne_zero X.p (X.S C0 CE1 CE2) b
    have hpe : ι ((X.p : ℚ_[X.p]) ^ e) = ((X.p : ℕ) : KK X.O) ^ e := by
      rw [map_zpow₀, map_natCast]
    have hp0 : ((X.p : ℕ) : KK X.O) ≠ 0 := by
      have := (vK_p X)
      intro h0
      rw [h0, valuation_zero_alt] at this
      exact WithTop.top_ne_coe this
    refine ⟨(padicValNat X.p sp : ℚ) + ((k : ℚ) * (1 / 2) + ((k : ℚ) * (1 / 2) + (e : ℚ) * 1)), ?_, ?_⟩
    · rw [hc, valuation_mul_alt, valuation_mul_alt, valuation_mul_alt, hpe, vK_zpow hp0 (vK_p X) e, hvlam,
        valuation_natCast_padicVal X.std.1.prime X.setting sp hsp0]
      simp only [← WithTop.coe_add]
    · have h1 : (padicValNat X.p sp : ℚ) + ((k : ℚ) * (1 / 2) + ((k : ℚ) * (1 / 2) + (e : ℚ) * 1)) = (F : ℚ) := by
        rw [hk']; simp only [Int.cast_sub, Int.cast_natCast]; ring
      rw [h1, hF]
      have := Int.floor_le ((D : ℝ) + levelPassageLoss X)
      exact_mod_cast this
  have hsm : ∀ (a : KK X.O) (u v : MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) (KK X.O)),
      blockForm X.O X.p X.r (X.S C0 CE1 CE2) b (a • u) v = a * blockForm X.O X.p X.r (X.S C0 CE1 CE2) b u v := by
    intro a u v
    unfold blockForm
    rw [fock_form_symm, fock_form_smul_right, fock_form_symm v u, smul_eq_mul]
    ring
  have hadd : ∀ (u u' v : MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) (KK X.O)),
      blockForm X.O X.p X.r (X.S C0 CE1 CE2) b (u + u') v = blockForm X.O X.p X.r (X.S C0 CE1 CE2) b u v + blockForm X.O X.p X.r (X.S C0 CE1 CE2) b u' v := by
    intro u u' v
    unfold blockForm
    rw [fock_form_symm, fock_form_add_right, fock_form_symm v u, fock_form_symm v u']
    ring
  exact goodSub_of_dual X.setting (blockForm X.O X.p X.r (X.S C0 CE1 CE2) b) hsm hadd
    (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b) (fun i => lam • map ι (x i)) (fun i => lam • map ι (y i))
    (fun i => hmemL _ (hx i)) (fun i => hmemL _ (hy i)) c hform _ hvc

theorem block_bound_of_dual_families (hZ : BlockBoundIntegers C0 CE1 CE2 X) (hdim : RestBCdim C0 CE1 CE2 X) : BlockBoundUniformiser C0 CE1 CE2 X := by
  intro aTop hT aPlus hP b hk D hD
  obtain ⟨n, x, y, e, hx, hy, hxy, hmon, hrk⟩ := hZ aTop hT aPlus hP b hk D hD
  obtain ⟨L₂, hg, hn⟩ := block_dual_family_bound C0 CE1 CE2 X aTop aPlus b D n x y e hx hy hxy hmon
  exact ⟨L₂, hg, (hdim aTop hT aPlus hP b hk).trans (hrk.trans (Nat.add_le_add_right hn _))⟩

end Assemble

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
end
