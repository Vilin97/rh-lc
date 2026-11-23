module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.CartierFrobeniusFormLocal
import GroundTheory.AutomorphicForms.AdelicGLn
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactClopenNhdsOneGLFiniteAdeles

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

open scoped RestrictedProduct

noncomputable section

namespace GlobalTheory.GLFinAdeleNhds

theorem totallyDisconnectedSpace_of_injective {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TotallyDisconnectedSpace Y] (f : X → Y) (hf : Continuous f) (hi : Function.Injective f) :
    TotallyDisconnectedSpace X := by
  refine ⟨fun s _ hs => ?_⟩
  have h := (hs.image f hf.continuousOn).subsingleton
  exact fun x hx y hy => hi (h (Set.mem_image_of_mem f hx) (Set.mem_image_of_mem f hy))

theorem totallyDisconnectedSpace_adicCompletion {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : TotallyDisconnectedSpace (v.adicCompletion F) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_zero]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, fun x hx => ?_⟩
  by_contra hne
  have hr : (Valued.v : Valuation (v.adicCompletion F) _).restrict x ≠ 0 :=
    (Valuation.zero_iff _).not.mpr hne
  have hc := Valued.isClopen_ball (R := v.adicCompletion F)
    ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)
  have h0 : (0 : v.adicCompletion F) ∈
      {y | (Valued.v : Valuation (v.adicCompletion F) _).restrict y <
        (Valued.v : Valuation (v.adicCompletion F) _).restrict x} := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact pos_iff_ne_zero.mpr hr
  have h1 := hc.connectedComponent_subset h0 hx
  exact (lt_irrefl ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)) h1

theorem totallyDisconnectedSpace_Af (E : Type) [Field E] [NumberField E] : TotallyDisconnectedSpace (Af E) := by
  haveI : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), TotallyDisconnectedSpace (v.adicCompletion E) :=
    fun v => totallyDisconnectedSpace_adicCompletion v
  haveI : TotallyDisconnectedSpace
      (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), [v.adicCompletion E, v.adicCompletionIntegers E]) :=
    totallyDisconnectedSpace_of_injective (fun x v => x v) (continuous_pi fun v => RestrictedProduct.continuous_eval v)
      fun x y h => Subtype.ext (funext fun v => congrFun h v)
  exact inferInstanceAs (TotallyDisconnectedSpace
    (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), [v.adicCompletion E, v.adicCompletionIntegers E]))

theorem exists_isCompact_isClopen (E : Type) [Field E] [NumberField E] (a : ℕ) (B : Set (GL (Fin a) (Af E)))
    (hB : B ∈ nhds (1 : GL (Fin a) (Af E))) :
    ∃ U : Set (GL (Fin a) (Af E)), IsOpen U ∧ IsCompact U ∧ IsClosed U ∧ 1 ∈ U ∧ U ⊆ B := by
  haveI := totallyDisconnectedSpace_Af E
  haveI : TotallyDisconnectedSpace (Matrix (Fin a) (Fin a) (Af E)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin a → Fin a → Af E))
  haveI : TotallyDisconnectedSpace (GL (Fin a) (Af E)) :=
    totallyDisconnectedSpace_of_injective _ Units.continuous_val Units.val_injective
  haveI : LocallyCompactSpace (GL (Fin a) (Af E)) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  obtain ⟨K, hK, hKB, hc⟩ := local_compact_nhds hB
  obtain ⟨U, hU, h1, hUK⟩ := loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 hK
  exact ⟨U, hU.2, hc.of_isClosed_subset hU.1 hUK, hU.1, h1, hUK.trans hKB⟩

end GlobalTheory.GLFinAdeleNhds
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactClopenNhdsOneGLFiniteAdelesStatement

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

theorem _root_.GlobalTheory.T.exists_compact_clopen_nhds_one_GL_finiteAdeles : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (B : Set (GL (Fin a) (Af E))), B ∈ nhds (1 : GL (Fin a) (Af E)) → ∃ U : Set (GL (Fin a) (Af E)), IsOpen U ∧ IsCompact U ∧ IsClosed U ∧ 1 ∈ U ∧ U ⊆ B := by
  first | exact @GlobalTheory.GLFinAdeleNhds.exists_isCompact_isClopen | exact GlobalTheory.GLFinAdeleNhds.exists_isCompact_isClopen | (intros; apply GlobalTheory.GLFinAdeleNhds.exists_isCompact_isClopen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenSubgroupSubsetNhdsOne

section

@[expose] public section

open NumberField MeasureTheory Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.GLFin

namespace GlobalTheory.GLFinSmall

open Set Filter Pointwise Topology

theorem exists_nhds_mul_subset {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {W : Set G} (hWc : IsCompact W) (hWo : IsOpen W) : ∃ T ∈ 𝓝 (1 : G), W * T ⊆ W := by
  apply hWc.induction_on (p := fun S ↦ ∃ T ∈ 𝓝 (1 : G), S * T ⊆ W)
    ⟨Set.univ, by simp only [univ_mem, Set.empty_mul, empty_subset, and_self]⟩
    (fun _ _ huv ⟨T, hT, mem⟩ ↦ ⟨T, hT, (mul_subset_mul_right huv).trans mem⟩)
    fun U V ⟨T₁, hT₁, mem1⟩ ⟨T₂, hT₂, mem2⟩ ↦ ⟨T₁ ∩ T₂, inter_mem hT₁ hT₂, by
      rw [union_mul]
      exact union_subset (mul_subset_mul_left inter_subset_left |>.trans mem1)
        (mul_subset_mul_left inter_subset_right |>.trans mem2)⟩
  intro x memW
  have : (x, 1) ∈ (fun p : G × G ↦ p.1 * p.2) ⁻¹' W := by simp [memW]
  rcases isOpen_prod_iff.mp (continuous_mul.isOpen_preimage W hWo) x 1 this with
    ⟨U, V, Uopen, Vopen, xmemU, onememV, prodsub⟩
  have h6 : U * V ⊆ W := mul_subset_iff.mpr (fun _ hx _ hy ↦ prodsub (mk_mem_prod hx hy))
  exact ⟨U ∩ W, ⟨U, Uopen.mem_nhds xmemU, W, fun _ a ↦ a, rfl⟩,
    V, IsOpen.mem_nhds Vopen onememV, fun _ a ↦ h6 ((mul_subset_mul_right inter_subset_left) a)⟩

def rightStab {G : Type} [Group G] (W : Set G) : Subgroup G where
  carrier := {g | ∀ w, w ∈ W ↔ w * g ∈ W}
  one_mem' := by intro w; simp
  mul_mem' := by
    intro g h hg hh w
    rw [hg w, hh (w * g), mul_assoc]
  inv_mem' := by
    intro g hg w
    rw [hg (w * g⁻¹), inv_mul_cancel_right]

theorem exists_compact_open_subgroup_subset {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {W : Set G} (hWc : IsCompact W) (hWo : IsOpen W) (h1 : (1 : G) ∈ W) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ IsCompact (U : Set G) ∧ (U : Set G) ⊆ W := by
  obtain ⟨T, hT, hTW⟩ := exists_nhds_mul_subset hWc hWo
  have hsub : T ∩ T⁻¹ ⊆ (rightStab W : Set G) := by
    intro v hv w
    constructor
    · intro hw; exact hTW (Set.mul_mem_mul hw hv.1)
    · intro hw
      have : w * v * v⁻¹ ∈ W := hTW (Set.mul_mem_mul hw (Set.mem_inv.mp hv.2))
      simpa using this
  have hnhds : (rightStab W : Set G) ∈ 𝓝 (1 : G) :=
    Filter.mem_of_superset (inter_mem hT (inv_mem_nhds_one G hT)) hsub
  have hopen : IsOpen (rightStab W : Set G) := Subgroup.isOpen_of_mem_nhds _ hnhds
  have hW : (rightStab W : Set G) ⊆ W := by
    intro g hg
    have := (hg 1).mp h1
    simpa using this
  refine ⟨rightStab W, hopen, ?_, hW⟩
  exact hWc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hopen) hW

end GlobalTheory.GLFinSmall

theorem GlobalTheory.GLFin.exists_compact_open_subgroup_subset_nhds_one :
    ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (B : Set (GL (Fin a) (Af E))),
      B ∈ nhds (1 : GL (Fin a) (Af E)) → ∃ U : Subgroup (GL (Fin a) (Af E)),
        IsOpen (U : Set (GL (Fin a) (Af E))) ∧ IsCompact (U : Set (GL (Fin a) (Af E))) ∧
          (U : Set (GL (Fin a) (Af E))) ⊆ B := by
  intro E _ _ a B hB
  obtain ⟨W, hWo, hWc, -, h1, hWB⟩ := GlobalTheory.T.exists_compact_clopen_nhds_one_GL_finiteAdeles E a B hB
  obtain ⟨U, hUo, hUc, hUW⟩ := GlobalTheory.GLFinSmall.exists_compact_open_subgroup_subset hWc hWo h1
  exact ⟨U, hUo, hUc, hUW.trans hWB⟩
end
end
