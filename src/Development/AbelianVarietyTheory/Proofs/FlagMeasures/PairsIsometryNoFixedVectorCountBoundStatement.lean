module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardIsometriesFixingSubspaceDefiniteLatticesLeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscriminantOrderCommonFixedLatticeEmbeddedDataStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardEmbeddedDataWithGivenFixedLattice
public import Formalism.HyperbolicPlaceProducts.SecondLevelArithmeticNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Set.Card.Arithmetic
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
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardEmbeddedHermDataIndexLe

section

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

theorem finrank_sub_le {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) :
    Module.finrank (𝓞 K) L ≤ Module.finrank K V := by
  apply Module.finrank_le_of_rank_le
  apply rank_le
  intro s hs
  have h := hs.map' L.subtype (Submodule.ker_subtype L)
  rw [LinearIndependent.iff_fractionRing (R := 𝓞 K) (K := K)] at h
  simpa using h.fintype_card_le_finrank

theorem sublat_count {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (hL : L.FG) (x : ℕ) (hx : 1 ≤ x) :
    {N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x}.Finite ∧
      (({N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x}.ncard : ℕ) : ℝ) ≤
        (x : ℝ) ^ (((Module.finrank K V) : ℝ) + cf K) := by
  have : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.2 hL
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.Flat (𝓞 K) L := inferInstance
  have : Module.FinitePresentation (𝓞 K) L := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨h1, h2⟩ := Formalism.SLP.Final.submoduleIndexCountO K L x hx
  have hsub : {N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x} ⊆
      (Submodule.map L.subtype) '' {N : Submodule (𝓞 K) L | N.toAddSubgroup.index = x} := by
    rintro N ⟨hN, hi⟩
    refine ⟨N.comap L.subtype, ?_, ?_⟩
    · exact hi
    · rw [Submodule.map_comap_subtype, inf_eq_right.2 hN]
  refine ⟨(h1.image _).subset hsub, ?_⟩
  have h3 := (Set.ncard_le_ncard hsub (h1.image _)).trans (Set.ncard_image_le h1)
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have h4 := Formalism.SLP.Final.omegaPow (Module.finrank ℚ K) x Module.finrank_pos hx
  have h5 : ((Module.finrank (𝓞 K) L : ℕ) : ℝ) ≤ (Module.finrank K V : ℝ) := by
    exact_mod_cast finrank_sub_le L
  calc (({N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x}.ncard : ℕ) : ℝ)
      ≤ ((Module.finrank ℚ K : ℕ) : ℝ) ^ (Nat.primeFactorsList x).length * (x : ℝ) ^ Module.finrank (𝓞 K) L := by
        exact_mod_cast h3.trans h2
    _ ≤ (x : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ Module.finrank (𝓞 K) L :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = (x : ℝ) ^ (((Module.finrank (𝓞 K) L : ℕ) : ℝ) + Real.logb 2 (Module.finrank ℚ K)) := by
        rw [Real.rpow_add hx0, Real.rpow_natCast, mul_comm]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by unfold cf; linarith)

theorem encard_isDat_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ x : ℕ, 1 ≤ x → ((({d | IsDat H g L₀ j x d}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((x : ℝ) ^ (((Module.finrank K V) : ℝ) + cf K) * ((x : ℝ) * D₀) ^ (3 * (2 * j + 1))) := by
  intro K V _ _ _ _ _ _ _ _ H hK hP L₀ g j D₀ hL hD hG hg x hx
  have hfib := GlobalTheory.DegCnt.DatCount.main K V H hK hP L₀ g j D₀ hL hD hG hg
  obtain ⟨hfin, hcnt⟩ := sublat_count L₀ hL.1.fg x hx
  set S := {N : Submodule (𝓞 K) V | N ≤ L₀ ∧ idx L₀ N = x} with hS
  have hsub : {d | IsDat H g L₀ j x d} ⊆
      ⋃ La ∈ hfin.toFinset, {d | IsDat H g L₀ j x d ∧ fixLat d.2 = La} := by
    intro d hd
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset]
    refine ⟨fixLat d.2, ⟨?_, hd.2.2.2.1⟩, hd, rfl⟩
    intro y hy
    exact (hd.2.2.1.1 hy).2
  have h1 := (Set.encard_le_encard hsub).trans (Finset.set_encard_biUnion_le _ _)
  have h2 : ((({d | IsDat H g L₀ j x d}).encard : ℕ∞) : ℝ≥0∞) ≤
      ∑ La ∈ hfin.toFinset, ((({d | IsDat H g L₀ j x d ∧ fixLat d.2 = La}).encard : ℕ∞) : ℝ≥0∞) := by
    refine (ENat.toENNReal_le.2 h1).trans (le_of_eq ?_)
    exact map_sum ENat.toENNRealRingHom _ _
  refine h2.trans ((Finset.sum_le_card_nsmul _ _ _ fun La _ => hfib La x).trans ?_)
  rw [nsmul_eq_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  gcongr
  rw [← ENNReal.ofReal_natCast, ← Set.ncard_eq_toFinset_card S hfin]
  exact ENNReal.ofReal_le_ofReal hcnt

end GlobalTheory.DegCnt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardEmbeddedHermDataIndexLeStatement

section

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.encard_embedded_hermData_index_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ x : ℕ, 1 ≤ x → ((({d | IsDat H g L₀ j x d}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((x : ℝ) ^ (((Module.finrank K V) : ℝ) + cf K) * ((x : ℝ) * D₀) ^ (3 * (2 * j + 1))) := by
  first | exact @GlobalTheory.DegCnt.encard_isDat_le | exact GlobalTheory.DegCnt.encard_isDat_le | (intros; apply GlobalTheory.DegCnt.encard_isDat_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairsIsometryNoFixedVectorCountBound

section

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.PairNoFix

theorem encard_le_of_fibres {α β : Type} (S : Set α) (T : Set β) (f : α → β) (hf : ∀ a ∈ S, f a ∈ T)
    (c : ℝ≥0∞) (hc : ∀ b ∈ T, ((({a ∈ S | f a = b}).encard : ℕ∞) : ℝ≥0∞) ≤ c) :
    ((S.encard : ℕ∞) : ℝ≥0∞) ≤ ((T.encard : ℕ∞) : ℝ≥0∞) * c := by
  rw [← ENNReal.tsum_set_one S, ← ENNReal.tsum_set_const,
    ← ENNReal.tsum_fiberwise (fun _ : S => (1 : ℝ≥0∞)) (fun a : S => (⟨f a, hf a a.2⟩ : T))]
  refine ENNReal.tsum_le_tsum fun b => ?_
  rw [ENNReal.tsum_set_one]
  refine le_trans ?_ (hc b b.2)
  rw [← (Subtype.val_injective.encard_image _)]
  refine ENat.toENNReal_le.2 (Set.encard_le_encard ?_)
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a.2, congrArg Subtype.val ha⟩

theorem arith (k f : ℕ) (c e : ℝ) (hc : 0 ≤ c) (x x' D q A : ℝ) (hx : 1 ≤ x) (hx' : 1 ≤ x') (hD : 1 ≤ D)
    (hq : 0 < q) (hA : 0 ≤ A) (h : 1 ≤ q ^ (2 * k * f) * D * x * x') (m : ℕ) (hm : (m : ℝ) = e) :
    (x ^ ((k : ℝ) + c) * (x * D) ^ m) * (x' ^ ((k : ℝ) + c) * (x' * D) ^ m) * A ^ (4 * k * f) ≤
      (x * x') ^ ((k : ℝ) / 2) * (x * x' * D ^ 2) ^ (c + e) * (q ^ (k * f) * A ^ (4 * f) * D * x * x') ^ k := by
  subst hm
  have x0 : 0 < x := by linarith
  have x0' : 0 < x' := by linarith
  have D0 : 0 < D := by linarith
  have h1 : 1 ≤ (x * x') ^ ((k : ℝ) / 2) * (q ^ (k * f) * D) ^ k := by
    have hs : ((x * x') ^ ((k : ℝ) / 2)) ^ 2 = (x * x') ^ k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
      congr 1; push_cast; ring
    have h2 : 1 ≤ ((x * x') ^ ((k : ℝ) / 2) * (q ^ (k * f) * D) ^ k) ^ 2 := by
      rw [mul_pow, hs]
      have : (x * x') ^ k * ((q ^ (k * f) * D) ^ k) ^ 2 = (q ^ (2 * k * f) * D * x * x') ^ k * D ^ k := by
        ring
      rw [this]
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ h) (one_le_pow₀ hD)
    exact (one_le_sq_iff₀ (by positivity)).1 h2
  have h3 : x ^ c * x' ^ c ≤ (x * x' * D ^ 2) ^ c := by
    rw [← Real.mul_rpow x0.le x0'.le]
    refine Real.rpow_le_rpow (by positivity) ?_ hc
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hD)
  rw [Real.rpow_add x0, Real.rpow_add x0', Real.rpow_add (by positivity : 0 < x * x' * D ^ 2)]
  simp only [Real.rpow_natCast]
  calc x ^ k * x ^ c * (x * D) ^ m * (x' ^ k * x' ^ c * (x' * D) ^ m) * A ^ (4 * k * f)
      = 1 * (x ^ c * x' ^ c) * ((x * x' * D ^ 2) ^ m * (A ^ (4 * f) * x * x') ^ k) := by ring
    _ ≤ ((x * x') ^ ((k : ℝ) / 2) * (q ^ (k * f) * D) ^ k) * (x * x' * D ^ 2) ^ c *
        ((x * x' * D ^ 2) ^ m * (A ^ (4 * f) * x * x') ^ k) := by gcongr
    _ = _ := by ring

theorem main : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' : ℕ), 1 ≤ x → 1 ≤ x' → ((({p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (((x : ℝ) * x') ^ (((Module.finrank K V) : ℝ) / 2) * ((x : ℝ) * x' * (D₀ : ℝ) ^ 2) ^ (cf K + 3 * (2 * j + 1)) * ((2 / (g : ℝ)) ^ ((Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)) * ((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x') ^ (Module.finrank K V)) := by
  intro hM K V _ _ _ _ _ _ _ _ H hK hPD L₀ g j D₀ hL hD hG hg x x' hx hx'
  rcases Set.eq_empty_or_nonempty {p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥} with he | ⟨p₀, hp₀, hfix⟩
  · rw [he]; simp
  have h43 := GlobalTheory.T.discriminantOrder_common_fixedLattice_embeddedData K V H hK hPD L₀ g j D₀ hL hD hG hg x x' hx hx' p₀ hp₀
  rw [hfix] at h43
  have hone : GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip (⊥ : Submodule K V))
      (GlobalTheory.Mass.latIn ⊥ (fixLat p₀.1.2)) = 1 := by
    unfold GlobalTheory.Mass.discN GlobalTheory.Mass.idxN
    rw [AddSubgroup.relIndex_eq_one]
    intro y _
    rw [Subsingleton.elim y 0]
    exact zero_mem _
  rw [hone, finrank_bot, Nat.sub_zero, Nat.cast_one] at h43
  have hD1 : 1 ≤ D₀ := by
    rcases Nat.eq_zero_or_pos D₀ with h | h
    · rw [h] at h43; norm_num at h43
    · exact h
  have hcf : 0 ≤ cf K := by
    unfold cf
    have : (1 : ℝ) ≤ Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    have := Real.logb_nonneg (b := 2) (by norm_num) this
    linarith
  have hA := GlobalTheory.T.encard_embedded_hermData_index_le K V H hK hPD L₀ g j D₀ hL hD hG hg x hx
  have hB := GlobalTheory.T.encard_embedded_hermData_index_le K V H hK hPD L₀ g j D₀ hL hD hG hg x' hx'
  have hcnt := encard_le_of_fibres {p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥}
    ({d | IsDat H g L₀ j x d} ×ˢ {d | IsDat H g L₀ j x' d}) (fun p => (p.1, p.2.1))
    (fun p hp => ⟨hp.1.1, hp.1.2.1⟩)
    (((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ≥0∞) ^ (4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)))
    (by
      rintro ⟨d, d'⟩ ⟨hd, hd'⟩
      have h := GlobalTheory.T.card_isometries_fixing_subspace_definite_lattices_le hM K V H hK hPD ⊥ d'.1 d.1 hd'.1.1 hd.1.1
      rw [finrank_bot, Nat.sub_zero] at h
      refine le_trans (ENat.toENNReal_le.2 ?_) h
      refine Set.encard_le_encard_of_injOn (f := fun p => p.2.2) ?_ ?_
      · rintro ⟨a, b, η⟩ ⟨⟨hp, -⟩, he⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        refine ⟨hp.2.2.1, hp.2.2.2.1, ?_⟩
        intro y hy
        rw [(Submodule.mem_bot K).1 hy, map_zero]
      · rintro ⟨a, b, η⟩ ⟨-, he⟩ ⟨a', b', η'⟩ ⟨-, he'⟩ hη
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he'
        simp only at hη
        rw [hη])
  rw [Set.encard_prod, ENat.toENNReal_mul] at hcnt
  refine hcnt.trans ((mul_le_mul_left (mul_le_mul' hA hB) _).trans ?_)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  exact arith _ _ _ _ hcf _ _ _ _ _ (by exact_mod_cast hx) (by exact_mod_cast hx') (by exact_mod_cast hD1)
    (by positivity) (by positivity) h43 _ (by push_cast; ring)

end GlobalTheory.PairNoFix
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairsIsometryNoFixedVectorCountBoundStatement

section

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.pairs_isometry_no_fixed_vector_count_bound : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' : ℕ), 1 ≤ x → 1 ≤ x' → ((({p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (((x : ℝ) * x') ^ (((Module.finrank K V) : ℝ) / 2) * ((x : ℝ) * x' * (D₀ : ℝ) ^ 2) ^ (cf K + 3 * (2 * j + 1)) * ((2 / (g : ℝ)) ^ ((Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)) * ((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x') ^ (Module.finrank K V)) := by
  first | exact @GlobalTheory.PairNoFix.main | exact GlobalTheory.PairNoFix.main | (intros; apply GlobalTheory.PairNoFix.main <;> assumption)
end
end
