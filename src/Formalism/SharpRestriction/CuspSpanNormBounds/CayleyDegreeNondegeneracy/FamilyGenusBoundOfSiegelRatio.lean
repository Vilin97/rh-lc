module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ShortVectorEveryPlace
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteDimensionalOfOrtho
public import Formalism.HermitianLattices.StatementMass
public import Formalism.HermitianLattices.FinalNeighbourConstruct
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.MassPowLeExpRpow
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ExistsSmallMemFractionalIdeal
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ProdNormEmbeddingsEqAbsNorm
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.TraceInnerPosOfOrthonormalPair
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Mathlib.Algebra.Module.StablyFree.Basic

-- Source module: Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenusOrthonormalIntegralUnimodular

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Formalism.HermitianLatticesTheory

section Gen

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem star_algebraMap_mem_range (r : 𝓞 K) : star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
  ⟨⟨star (algebraMap (𝓞 K) K r), r.isIntegral_coe.map (starRingEnd K).toIntAlgHom⟩, rfl⟩

theorem inner_sum_orthonormal (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ} (e : Fin n → V)
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (a b : Fin n → K) :
    h (∑ i, a i • e i) (∑ j, b j • e j) = ∑ i, star (a i) * b i := by

  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, he,
  smul_eq_mul, starRingEnd_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

theorem fg_of_orthonormal_basis (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) {n : ℕ} (hL : IsOrthoLattice h L n) : L.FG := by
  obtain ⟨e, -, -, rfl, -⟩ := hL
  exact Submodule.fg_span (Set.finite_range e)

theorem integral_of_orthonormal_basis (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) {n : ℕ} (hL : IsOrthoLattice h L n) :
    IsIntegralLat h L := by
  obtain ⟨e, -, -, rfl, he⟩ := hL
  intro x hx y hy
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hx
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hy
  have e1 : ∑ i, a i • e i = ∑ i, (algebraMap (𝓞 K) K (a i)) • e i :=
    Finset.sum_congr rfl fun i _ => (algebraMap_smul K (a i) (e i)).symm
  have e2 : ∑ i, b i • e i = ∑ i, (algebraMap (𝓞 K) K (b i)) • e i :=
    Finset.sum_congr rfl fun i _ => (algebraMap_smul K (b i) (e i)).symm
  rw [e1, e2, inner_sum_orthonormal h e he]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨a', ha'⟩ := star_algebraMap_mem_range (a i)
  rw [← ha', ← map_mul]
  exact Submodule.mem_one.2 ⟨_, rfl⟩

theorem unimodular_of_orthonormal_basis (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) {n : ℕ} (hL : IsOrthoLattice h L n) :
    IsUnimodular h L := by
  apply Formalism.HermitianLattices.Ext.L3.isUnimodular_of_ortho <;> assumption

theorem genus_orthonormal_integral_unimodular (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (L : Submodule (𝓞 K) V) {n : ℕ} (hL : IsOrthoLattice h L n)
    (M : Submodule (𝓞 K) V) (hM : M ∈ genus h L) : IsIntegralLat h M ∧ dual h M = M := by
  have hG := (final_genusBasic (𝓞 K) K V h hs star_algebraMap_mem_range).2.2 L M (fg_of_orthonormal_basis h L hL) hM.1.fg hM.2
  exact ⟨hG.2.1 (integral_of_orthonormal_basis h L hL), hG.1.1 (unimodular_of_orthonormal_basis h L hL)⟩

theorem mass_le_of_card_class_reps_le (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (B : ℝ) (hB : 0 ≤ B)
    (hc : ∀ s, Formalism.ThetaLiftIndependence.IsClassReps h L s → (s.card : ℝ) ≤ B) : mass h L ≤ B := by
  classical
  unfold mass
  split_ifs with hs
  · refine le_trans ?_ (hc _ hs.choose_spec)
    calc ∑ M ∈ hs.choose, ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ ≤ ∑ M ∈ hs.choose, (1 : ℝ) := by
          refine Finset.sum_le_sum fun M _ => ?_
          rcases Nat.eq_zero_or_pos (Nat.card (Formalism.ThetaLiftIndependence.autL h M)) with h0 | h0
          · rw [h0]; simp
          · exact inv_le_one_of_one_le₀ (by exact_mod_cast h0)
      _ = (hs.choose.card : ℝ) := by simp
  · exact hB

end Gen

end Formalism.MainNotions.BridgeLemma₂

end
end
end

-- Source module: Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.PlaneMassBoundOfFacts

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.HermitianLatticesTheory

def SecondOrthogonalVector (K : Type) [Field K] [NumberField K] [StarRing K] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V), h.IsSymm → IsOrthoLattice h L 2 →
    ∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M → IsIntegralLat h M → dual h M = M →
    ∀ x ∈ M, x ≠ 0 → ∃ y ∈ M, y ≠ 0 ∧ h x y = 0 ∧ ∀ φ : K →+* ℂ, ‖φ (h y y)‖ ≤ ‖φ (h x x)‖ * rootDiscriminant K

def PlaneClassCount (K : Type) [Field K] [NumberField K] [StarRing K] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V), h.IsSymm → IsOrthoLattice h L 2 →
    ∀ s : Finset (Submodule (𝓞 K) V), Formalism.ThetaLiftIndependence.IsClassReps h L s → ∀ B₁ B₂ : ℝ,
    (∀ M ∈ s, IsIntegralLat h M) →
    (∀ M ∈ s, ∃ x ∈ M, ∃ y ∈ M, x ≠ 0 ∧ y ≠ 0 ∧ h x y = 0 ∧
      ∀ φ : K →+* ℂ, ‖φ (h x x)‖ ≤ B₁ ∧ ‖φ (h y y)‖ ≤ B₂) →
    (s.card : ℝ) ≤ (1 + 2 * B₁) ^ (2 * finrank ℚ K) * (1 + 2 * B₂) ^ (2 * finrank ℚ K) *
      (B₁ * B₂) ^ (4 * finrank ℚ K)

theorem card_class_reps_plane_le (K : Type) [Field K] [NumberField K] [StarRing K] (B₁ : ℝ)
    (hA : ShortVectorEveryPlace K B₁) (hB : SecondOrthogonalVector K) (hC : PlaneClassCount K) (hrd : 0 ≤ rootDiscriminant K)
    (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (hs : h.IsSymm) (hL : IsOrthoLattice h L 2)
    (s : Finset (Submodule (𝓞 K) V)) (hreps : Formalism.ThetaLiftIndependence.IsClassReps h L s) :
    (s.card : ℝ) ≤ (1 + 2 * B₁) ^ (2 * finrank ℚ K) * (1 + 2 * (B₁ * rootDiscriminant K)) ^ (2 * finrank ℚ K) *
      (B₁ * (B₁ * rootDiscriminant K)) ^ (4 * finrank ℚ K) := by
  refine hC V h L hs hL s hreps B₁ (B₁ * rootDiscriminant K)
    (fun M hM => (genus_orthonormal_integral_unimodular h hs L hL M (hreps.1 M hM)).1) fun M hM => ?_
  have hg := hreps.1 M hM
  have hMlat : Submodule.IsLattice K M := hg.1.toIsLattice
  obtain ⟨hint, huni⟩ := genus_orthonormal_integral_unimodular h hs L hL M hg
  obtain ⟨x, hx, hx0, hxB⟩ := hA V h L hs hL M hg
  obtain ⟨y, hy, hy0, hxy, hyB⟩ := hB V h L hs hL M hMlat hint huni x hx hx0
  exact ⟨x, hx, y, hy, hx0, hy0, hxy, fun φ =>
    ⟨hxB φ, (hyB φ).trans (mul_le_mul_of_nonneg_right (hxB φ) hrd)⟩⟩

end Formalism.MainNotions.BridgeLemma₂

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem plane_mass_bound_of_facts (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C B₁ : ℝ)
    (hA : ShortVectorEveryPlace D.host.E B₁) (hB : SecondOrthogonalVector D.host.E) (hCt : PlaneClassCount D.host.E)
    (hB0 : 0 ≤ B₁) (hB1 : B₁ ≤ 4 * D.R.f * D.host.rdE) (hC : 55 * max 1 (1 / Cl) ≤ C ^ 2)
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) : UnitaryVolumeMass.Mass2At D large₂ C := by
  intro V _ _ _ _ h L hs ho
  obtain ⟨-, -, h3, -, h5, -, -, -, -, -, h11, -, -, -, -, -, -, -, h19, -⟩ := hH
  have hm := D.R.two_le_m
  have hf : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) h3
  have hL1 : 1 ≤ large₂.sc.L := by
    unfold Scale.L
    exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hrd : 2 ≤ D.host.rdE := by
    have e : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
    rw [← e]; linarith
  have hlrd : Real.log D.host.rdE ≤ max 1 (1 / Cl) * large₂.sc.L := by
    refine le_trans h11 ?_
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
  have hlf : Real.log (D.R.f : ℝ) ≤ (D.R.m : ℝ) := by
    refine le_trans h5 ?_
    rw [Real.sqrt_le_left (by positivity)]
    have h1 : D.R.rS ≤ D.R.m := by unfold Ranks.rS; omega
    have h2 : (D.R.rS : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast h1
    have h3 : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast hm
    nlinarith
  have hrdE : rootDiscriminant D.host.E = D.host.rdE := rfl
  have hnum := mass_pow_le_exp_rpow D.R.f D.R.m D.host.rdE large₂.sc.L B₁ C (max 1 (1 / Cl)) hf hm hrd hL1 (le_max_left _ _) hlf hlrd hB0 hB1 hC
  have hb : large₂.sc.b = Real.exp large₂.sc.L := rfl
  rw [hb]
  refine mass_le_of_card_class_reps_le h L _ (by positivity) fun s hreps => ?_
  have hc := card_class_reps_plane_le D.host.E B₁ hA hB hCt (by rw [hrdE]; linarith) V h L hs ho s hreps
  rw [hrdE, Formalism.MainNotions.StandardLattice.finrank_host] at hc
  exact hc.trans hnum

end Formalism.MainNotions.BridgeLemma₂

end
end
end

-- Source module: Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FamilyGenusBoundOfSiegelRatio

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.HermitianLatticesTheory

theorem second_orthogonal_vector_holds (K : Type) [Field K] [NumberField K] [StarRing K] (hK : IsCMUnram K) : SecondOrthogonalVector K :=
  by
    classical
    intro V _ _ _ _ h L hs hL M hlat hint huni x hx hx0
    obtain ⟨e, he, hspan, hLe, ho⟩ := hL
    let b : Basis (Fin 2) K V := Basis.mk he (by rw [hspan])
    have hfull : Submodule.IsFullLattice K M := by
      refine { toIsLattice := hlat, span_eq_top := ?_ }
      apply Submodule.dualAnnihilator_eq_bot_iff.mp
      apply le_antisymm ?_ bot_le
      intro f hf
      let v : V := ∑ i : Fin 2, star (f (e i)) • e i
      have hpair : h v = f := by
        apply b.ext
        intro i
        fin_cases i <;> simp [v, LinearMap.map_smulₛₗ, starRingEnd_apply, ho, b, Basis.coe_mk]
      have hline (r : K) : r • v ∈ M := by
        rw [← huni]
        simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
        intro y hy
        have hy0 : h v y = 0 := by
          rw [hpair]
          exact (Submodule.mem_dualAnnihilator f).mp hf y (Submodule.subset_span hy)
        have hz : h y v = 0 := by simpa [hy0] using (hs.eq v y).symm
        simp [hz]
      have hv : v = 0 := by
        by_contra hv
        obtain ⟨i, hi⟩ : ∃ i, b.repr v i ≠ 0 := by
          by_contra hn
          push_neg at hn
          apply hv
          apply b.repr.injective
          ext i
          simp [hn i]
        let c := ((Finsupp.lapply i).comp b.repr.toLinearMap).restrictScalars (𝓞 K)
        have htop : M.map c = ⊤ := by
          rw [eq_top_iff]
          intro a _
          refine ⟨(a / b.repr v i) • v, hline _, ?_⟩
          simp [c, div_mul_cancel₀ _ hi]
        have : Module.Finite (𝓞 K) K := Module.finite_def.mpr (htop ▸ hlat.fg.map c)
        exact RingOfIntegers.not_isField K
          (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 K) K) (Field.toIsField K))
      rw [Submodule.mem_bot]
      simpa [hv] using hpair.symm
    exact exists_orthogonal_second_vector K hK V h L ⟨e, he, hspan, hLe, ho⟩ M hfull hint huni x hx hx0

theorem plane_class_count_holds (K : Type) [Field K] [NumberField K] [StarRing K] (hK : IsCMUnram K) : PlaneClassCount K :=
  fun V _ _ _ _ h L hs hL s hreps B₁ B₂ hint hshort => class_count_plane_bound K hK V h L hs hL s hreps B₁ B₂ hint hshort

end Formalism.MainNotions.BridgeLemma₂

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem plane_mass_le_height_pow (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C : ℝ)
    (hC : 55 * max 1 (1 / Cl) ≤ C ^ 2) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) : UnitaryVolumeMass.Mass2At D large₂ C := by
  have hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := D.sp.cm.cmUnram
  have hfin := Formalism.MainNotions.StandardLattice.finrank_host D
  have hrd : rootDiscriminant D.host.E = D.host.rdE := rfl
  have h19 : 1 ≤ D.host.v := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h19, -⟩ := hH
    exact h19
  have hrd0 : 0 ≤ D.host.rdE := by
    have e : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
    rw [← e]; linarith
  refine plane_mass_bound_of_facts D large₂ C' Cl Cg cb Cu cT CT C _ (short_vector_every_place D.host.E hK)
    (second_orthogonal_vector_holds D.host.E hK) (plane_class_count_holds D.host.E hK) ?_ ?_ hC hH
  · rw [hrd]; positivity
  · rw [hrd, hfin]; push_cast; apply le_of_eq; ring

theorem plane_mass_bound_parameters (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ)
    (hC : 55 * max 1 (1 / Cl) ≤ C ^ 2) : UnitaryVolumeMass.stMass2 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C :=
  fun hH => plane_mass_le_height_pow D large₂ C' Cl Cg cb Cu cT CT C hC hH.1.1

section Family

variable {eps : ℝ} (Fm : FamP eps)

end Family

end Formalism.MainNotions.BridgeLemma₂

end
end
end
