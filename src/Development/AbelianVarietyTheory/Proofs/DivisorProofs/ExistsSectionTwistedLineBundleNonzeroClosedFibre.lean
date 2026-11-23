module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTwistNonvanishingRationalPointStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankOfIsSecBasis
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingTwistedSectionsDescendFieldExtension

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TwistDescent

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gs gs_eq gs_mul gs_pull gs_res gs_compat mem_pull chartPullOut chartPullUnpull)

theorem ker_descend {k K : Type} [Field k] [Field K] [Algebra k K] {a b : ℕ}
    (D : Matrix (Fin b) (Fin a) k) (v : Fin a → K) (hv : (D.map (algebraMap k K)).mulVec v = 0) :
    ∃ (r : ℕ) (e : Fin r → K) (u : Fin r → Fin a → k), (∀ l, D.mulVec (u l) = 0) ∧
      ∀ j, v j = ∑ l, e l * algebraMap k K (u l j) := by
  classical
  let V := Submodule.span k (Set.range v)
  haveI : Module.Finite k V := FiniteDimensional.span_of_finite k (Set.finite_range v)
  let bV := Module.finBasis k V
  have hv' : ∀ j, v j ∈ V := fun j => Submodule.subset_span ⟨j, rfl⟩
  have hli : LinearIndependent k (fun l => (bV l : K)) :=
    bV.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank k V) → Fin a → k, ∀ j, v j = ∑ l, c l j • (bV l : K) :=
    ⟨fun l j => bV.repr ⟨v j, hv' j⟩ l, fun j => by
      have := congrArg Subtype.val (bV.sum_repr ⟨v j, hv' j⟩)
      rw [Submodule.coe_sum] at this
      simpa using this.symm⟩
  refine ⟨_, fun l => (bV l : K), c, fun l => ?_, fun j => ?_⟩
  · funext p
    have hp := congrFun hv p
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply, hc, Finset.mul_sum] at hp
    rw [Finset.sum_comm] at hp
    have : ∑ l, (∑ j, D p j * c l j) • (bV l : K) = 0 := by
      rw [← hp]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      ring
    exact Fintype.linearIndependent_iff.1 hli _ this l
  · rw [hc j]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Algebra.smul_def, mul_comm]

theorem mem_nonzeroLocus_iff_isUnit {X Z : Scheme.{0}} {N : LB X} (s : LB.Sec N) (r : Z ⟶ X) (z : Z) {j : N.ι}
    (hj : r z ∈ N.U j) : r z ∈ nonzeroLocus s ↔ IsUnit (gs r z _ (s.f j)) := by
  have key : ∀ {j : N.ι} (hj : r z ∈ N.U j), IsUnit (gs r z _ (s.f j)) ↔ r z ∈ X.basicOpen (s.f j) := by
    intro j hj
    rw [gs_eq r z _ hj]
    refine ((Z.mem_basicOpen ((r.app _).hom (s.f j)) z hj).symm).trans ?_
    rw [← Scheme.Hom.preimage_basicOpen]
    rfl
  rw [key hj]
  refine ⟨fun h => ?_, fun h => TopologicalSpace.Opens.mem_iSup.2 ⟨j, h⟩⟩
  obtain ⟨j', hj'⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  have hm : r z ∈ N.U j' := X.basicOpen_le _ hj'
  rw [← key hj, gs_compat s r z hj hm]
  exact (Units.isUnit _).mul ((key hm).2 hj')

theorem linComb_whisker {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (q : ℕ)
    {T T' : Over S} (ρ : T' ⟶ T) (c : T ⟶ A) :
    LB.LinComb L (K := Fin 2) (fun k => (ρ ▷ A).left ≫ ![(snd T A).left, (translPt A c).left] k)
      ![(q : ℤ) - 1, 1] = twistLB A L q (ρ ≫ c) := by
  unfold twistLB
  congr 1
  funext k
  fin_cases k
  · show (ρ ▷ A).left ≫ (snd T A).left = (snd T' A).left
    rw [← Over.comp_left, whiskerRight_snd]
  · show (ρ ▷ A).left ≫ (translPt A c).left = (translPt A (ρ ≫ c)).left
    rw [← Over.comp_left]
    congr 1
    simp [translPt, comp_lift_assoc]

theorem exists_sec_of_baseChange : ∀ (S : Scheme.{0}) (P : PolAV S) (k : Type) [Field k] (K : Type) [Field K] [Algebra k K] (t : Spec (CommRingCat.of k) ⟶ S) (c : Over.mk t ⟶ P.A), (∀ z : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t) ⊗ P.A).left, ∃ s : LB.Sec (twistLB P.A P.L 2 ((Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K))) rfl : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t) ⟶ Over.mk t) ≫ c)), z ∈ nonzeroLocus s) → ∀ y : (Over.mk t ⊗ P.A).left, ∃ s : LB.Sec (twistLB P.A P.L 2 c), y ∈ nonzeroLocus s := by
  intro S P k _ K _ _ t c hK y
  classical
  let ιK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let T := Over.mk t
  let h : Over.mk (ιK ≫ t) ⟶ T := Over.homMk ιK rfl
  rw [← linComb_whisker P.A P.L 2 h c] at hK
  let M : LB (T ⊗ P.A).left := twistLB P.A P.L 2 c
  have hM : M.IsLB := LB.isLB_linComb P.isLB _ _
  let f : (T ⊗ P.A).left ⟶ Spec (CommRingCat.of k) := (fst T P.A).left
  let π := (h ▷ P.A).left
  let f' : (Over.mk (ιK ≫ t) ⊗ P.A).left ⟶ Spec (CommRingCat.of K) := (fst (Over.mk (ιK ≫ t)) P.A).left
  have H : IsPullback π f' f ιK := GlobalTheory.AbLaw.SecBC.isPullback_whisker P.A h
  have hpb := GlobalTheory.AbLaw.SecBC.isPullback_snd P.A T
  haveI : IsProper f := MorphismProperty.of_isPullback (P := @IsProper) hpb P.isAb.proper
  haveI : Smooth f := MorphismProperty.of_isPullback (P := @Smooth) hpb P.isAb.smooth
  haveI : Flat f := inferInstance
  obtain ⟨Q⟩ := GlobalTheory.ProperFinite.nonempty_perf_of_isProper f hM
  haveI hι : Surjective ιK := ⟨fun p => ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩
  have hπ : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) H.flip hι
  obtain ⟨z, rfl⟩ := hπ.surj y
  by_contra hy
  push Not at hy
  obtain ⟨sK, hsK⟩ := hK z
  obtain ⟨i, hi⟩ := GlobalTheory.SecTwist.perf_cover Q (π z)
  have m₁ : π z ∈ M.U (Q.ch i) := Q.le i hi
  have m₂ : z ∈ (LB.LinComb P.L (K := Fin 2) (fun k => π ≫ ![(snd T P.A).left, (translPt P.A c).left] k)
      ![((2 : ℕ) : ℤ) - 1, 1]).U (Q.ch i) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 m₁ k
  let sb : LB.Sec (M.pull π) := GlobalTheory.SecTwist.pullSec (chartPullOut P.L _ _ π _ fun _ => rfl) sK
  obtain ⟨E, hE⟩ := GlobalTheory.SecTwist.perf_sec Q (algebraMap k K) H
  have hu1 : IsUnit (gs (𝟙 _) z ((M.pull π).U (fun _ => Q.ch i)) (sb.f (fun _ => Q.ch i))) := by
    have a₁ := GlobalTheory.SecTwist.gs_pullSec (chartPullOut P.L _ _ π _ fun _ => rfl) sK (𝟙 _) z (fun _ => Q.ch i)
      (mem_pull.2 m₁)
    rw [Category.id_comp] at a₁
    refine a₁ ▸ (mem_nonzeroLocus_iff_isUnit sK (𝟙 _) z m₂).1 hsK
  obtain ⟨r, e, u, hu, hvu⟩ := ker_descend Q.D₀ (E.symm sb).1 (E.symm sb).2
  have h₀ : IsPullback (𝟙 _) f f (Spec.map (CommRingCat.ofHom (RingHom.id k))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E₀, hE₀⟩ := GlobalTheory.SecTwist.perf_sec Q (RingHom.id k) h₀
  have ker : ∀ l, (Q.D₀.map (RingHom.id k)).mulVec (u l) = 0 := fun l => by
    rw [show Q.D₀.map (RingHom.id k) = Q.D₀ from rfl]
    exact hu l
  let s : Fin r → LB.Sec M := fun l => GlobalTheory.SecTwist.pullSec (chartPullUnpull M (𝟙 _) rfl) (E₀ ⟨u l, ker l⟩)
  have hG : ∀ l, gs π z (M.U (Q.ch i)) ((s l).f (Q.ch i)) =
      ∑ j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst (π ≫ f) z (u l j) * gs π z (Q.W i) (Q.u j i) := fun l => by
    have a₃ := GlobalTheory.SecTwist.gs_pullSec (chartPullUnpull M (𝟙 _) rfl) (E₀ ⟨u l, ker l⟩) π z (Q.ch i) m₁
    have a₄ := hE₀ ⟨u l, ker l⟩ i _ π z hi
    rw [Category.comp_id] at a₃ a₄
    exact a₃.trans a₄
  have hnu : ∀ l, gs π z (M.U (Q.ch i)) ((s l).f (Q.ch i)) ∈ IsLocalRing.maximalIdeal _ := fun l => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← mem_nonzeroLocus_iff_isUnit (s l) π z m₁]
    exact hy (s l)
  have e1 : ∀ a : k, ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst f' z (algebraMap k K a) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst (π ≫ f) z a :=
    fun a => by
      rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst_comp]
      congr 1
      exact H.w.symm
  have hsb := hE (E.symm sb) i _ (𝟙 _) z hi
  rw [Equiv.apply_symm_apply] at hsb

  simp only [Category.id_comp, hvu, ← GlobalTheory.SecTwist.cstHom_apply, map_sum, map_mul] at hsb
  simp only [GlobalTheory.SecTwist.cstHom_apply, e1] at hsb
  refine (IsLocalRing.mem_maximalIdeal _).1 ?_ hu1
  rw [hsb]
  have key : ∀ l, ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst f' z (e l) * gs π z (M.U (Q.ch i)) ((s l).f (Q.ch i)) ∈
      IsLocalRing.maximalIdeal _ := fun l => Ideal.mul_mem_left _ _ (hnu l)
  have := Ideal.sum_mem (IsLocalRing.maximalIdeal _) fun l (_ : l ∈ Finset.univ) => key l
  simp only [hG, Finset.mul_sum] at this
  rw [Finset.sum_comm] at this
  convert this using 2 with j
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.TwistDescent
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingTwistedSectionsDescendFieldExtensionStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.nonvanishing_twistedSections_descend_fieldExtension : ∀ (S : Scheme.{0}) (P : PolAV S) (k : Type) [Field k] (K : Type) [Field K] [Algebra k K] (t : Spec (CommRingCat.of k) ⟶ S) (c : Over.mk t ⟶ P.A), (∀ z : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t) ⊗ P.A).left, ∃ s : LB.Sec (twistLB P.A P.L 2 ((Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K))) rfl : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t) ⟶ Over.mk t) ≫ c)), z ∈ nonzeroLocus s) → ∀ y : (Over.mk t ⊗ P.A).left, ∃ s : LB.Sec (twistLB P.A P.L 2 c), y ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.TwistDescent.exists_sec_of_baseChange | exact GlobalTheory.TwistDescent.exists_sec_of_baseChange | (intros; apply GlobalTheory.TwistDescent.exists_sec_of_baseChange <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateTensorFibreNonvanishing

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TwistFibreGen

theorem exists_sec_of_closed {X : Scheme.{0}} [CompactSpace X] (M : LB X)
    (h : ∀ z : X, IsClosed ({z} : Set X) → ∃ s : LB.Sec M, z ∈ nonzeroLocus s) (z : X) :
    ∃ s : LB.Sec M, z ∈ nonzeroLocus s := by
  by_contra hz
  push_neg at hz
  let C : Set X := ⋂ s : LB.Sec M, ((nonzeroLocus s : X.Opens) : Set X)ᶜ
  have hC : IsClosed C := isClosed_iInter fun s => (nonzeroLocus s).isOpen.isClosed_compl
  obtain ⟨w, hw, hcl⟩ := hC.exists_closed_singleton ⟨z, Set.mem_iInter.2 fun s => hz s⟩
  obtain ⟨s, hs⟩ := h w hcl
  exact Set.mem_iInter.1 hw s hs

theorem compactSpace_fibre {S : Scheme.{0}} (P : PolAV S) (k : Type) [Field k]
    (t : Spec (CommRingCat.of k) ⟶ S) : CompactSpace (Over.mk t ⊗ P.A).left := by
  have := P.isAb.proper
  have : QuasiCompact (pullback.fst t P.A.hom) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst t P.A.hom)

theorem exists_sec_algClosed {S : Scheme.{0}} (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K]
    (t : Spec (CommRingCat.of K) ⟶ S) (c : Over.mk t ⟶ P.A) (z : (Over.mk t ⊗ P.A).left) :
    ∃ s : LB.Sec (twistLB P.A P.L 2 c), z ∈ nonzeroLocus s := by
  have := compactSpace_fibre P K t
  refine exists_sec_of_closed _ (fun z hz => ?_) z
  have := P.isAb.smooth
  have : LocallyOfFiniteType (fst (Over.mk t) P.A).left :=
    (inferInstance : LocallyOfFiniteType (pullback.fst t P.A.hom))
  let f := (fst (Over.mk t) P.A).left
  let p₀ := pointOfClosedPoint f z hz
  have hw : p₀ ≫ (Over.mk t ⊗ P.A).hom = (Over.mk t).hom := by
    rw [← Over.w (fst (Over.mk t) P.A), ← Category.assoc, pointOfClosedPoint_comp]
    exact Category.id_comp _
  let q : Over.mk t ⟶ Over.mk t ⊗ P.A := Over.homMk p₀ hw
  have hq : q ≫ fst (Over.mk t) P.A = 𝟙 _ := by
    ext1
    exact pointOfClosedPoint_comp f z hz
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_section_twist_nonvanishing_rationalPoint S P K t c (q ≫ snd _ _) (IsLocalRing.closedPoint _)
  refine ⟨s, ?_⟩
  have e : lift (𝟙 (Over.mk t)) (q ≫ snd (Over.mk t) P.A) = q := by
    rw [← hq, lift_comp_fst_snd]
  rw [e] at hs
  have h2 : q.left (IsLocalRing.closedPoint K) = z := pointOfClosedPoint_apply f z hz _
  rw [← h2]
  exact hs

theorem exists_sec_mem_nonzeroLocus : ∀ (S : Scheme.{0}) (P : PolAV S) (k : Type) [Field k]
    (t : Spec (CommRingCat.of k) ⟶ S) (c : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left),
    ∃ s : LB.Sec (twistLB P.A P.L 2 c), y ∈ nonzeroLocus s := by
  intro S P k _ t c y
  exact GlobalTheory.T.nonvanishing_twistedSections_descend_fieldExtension S P k (AlgebraicClosure k) t c (fun z => exists_sec_algClosed P _ _ _ z) y

end GlobalTheory.TwistFibreGen
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateTensorFibreNonvanishingStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_section_translateTensor_fibre_nonvanishing : ∀ (S : Scheme.{0}) (P : PolAV S) (k : Type) [Field k] (t : Spec (CommRingCat.of k) ⟶ S) (c : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left), ∃ s : LB.Sec (twistLB P.A P.L 2 c), y ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.TwistFibreGen.exists_sec_mem_nonzeroLocus | exact GlobalTheory.TwistFibreGen.exists_sec_mem_nonzeroLocus | (intros; apply GlobalTheory.TwistFibreGen.exists_sec_mem_nonzeroLocus <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTwistedLineBundleNonzeroClosedFibre

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TwistGen

theorem whisker_eq_twistLB {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (q : ℕ)
    {T T' : Over S} (ρ : T' ⟶ T) (c : T ⟶ A) :
    LB.LinComb L (K := Fin 2) (fun k => (ρ ▷ A).left ≫ ![(snd T A).left, (translPt A c).left] k)
      ![(q : ℤ) - 1, 1] = twistLB A L q (ρ ≫ c) := by
  unfold twistLB
  congr 1
  funext k
  fin_cases k
  · show (ρ ▷ A).left ≫ (snd T A).left = (snd T' A).left
    rw [← Over.comp_left, whiskerRight_snd]
  · show (ρ ▷ A).left ≫ (translPt A c).left = (translPt A (ρ ≫ c)).left
    rw [← Over.comp_left]
    congr 1
    simp [translPt, comp_lift_assoc]

theorem mem_of_isPullSecLC {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : Y' ⟶ Y) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε))
    (hs : IsPullSecLC L φ ε h s s') (y : Y') (hy : y ∈ nonzeroLocus s') : h y ∈ nonzeroLocus s := by
  obtain ⟨(j : K → L.ι), hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  rw [hs j] at hj
  erw [Scheme.basicOpen_res] at hj
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (Scheme.preimage_basicOpen h (s.f j)).ge hj.2⟩

theorem transfer {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (α : D.X)
    (s : LB.Sec (twistLB D.P.A D.P.L 2 (D.c α)))
    (z : (𝟙_ (Over (Spec (CommRingCat.of R))) ⊗ D.P.A).left) (hz : z ∈ nonzeroLocus s) :
    ∃ σ : D.SecB 2 α, (snd _ D.P.A).left z ∈ nonzeroLocus σ := by
  let T := 𝟙_ (Over (Spec (CommRingCat.of R)))
  let A := D.P.A
  let iota : A.left ⟶ (T ⊗ A).left := (lift (toUnit A) (𝟙 A)).left
  have hsec : snd T A ≫ lift (toUnit A) (𝟙 A) = 𝟙 (T ⊗ A) := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · exact (toUnit_unique _ _)
    · rw [Category.assoc, lift_snd, Category.comp_id, Category.id_comp]
  have hiota : iota ((snd T A).left z) = z := by
    have e : (snd T A).left ≫ iota = 𝟙 _ := by rw [← Over.comp_left, hsec]; rfl
    have e' := congrArg (fun f => f.base z) e
    exact e'
  obtain ⟨u₀, hu₀⟩ := DVR.exists_gen_of_local (V := R) D.P.L D.P.isLB (K := Fin 2)
    (![(D.c α).left, η[A].left] : Fin 2 → (Spec (CommRingCat.of R) ⟶ A.left)) ![-1, 1]
  let u := LB.pullGen D.P.L _ _ u₀ (toUnit A).left
  have hu : u.IsGen := DVR.pullGen_isGen_of_isGen _ _ u₀ hu₀ _
  let s₁ := pullMulSec s iota u hu
  have hF : FormEq (Sum.elim (fun k => iota ≫ ![(snd T A).left, (translPt A (D.c α)).left] k)
      (fun k => (toUnit A).left ≫ (![(D.c α).left, η[A].left] : Fin 2 → (Spec (CommRingCat.of R) ⟶ A.left)) k))
      (Sum.elim ![((2 : ℕ) : ℤ) - 1, 1] ![-1, 1]) (D.famφB α) (DegPre.famε 2) := by
    have e₁ : iota ≫ (snd T A).left = 𝟙 _ := by
      rw [← Over.comp_left, lift_snd]; rfl
    have e₂ : iota ≫ (translPt A (D.c α)).left = (padd A (𝟙 A) (toUnit A ≫ D.c α)).left := by
      rw [← Over.comp_left]
      congr 1
      show lift (toUnit A) (𝟙 A) ≫ ((fst T A ≫ D.c α) * snd T A) = 𝟙 A * (toUnit A ≫ D.c α)
      rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift, lift_snd, ← Category.assoc, lift_fst]
      show (toUnit A ≫ D.c α) * 𝟙 A = 𝟙 A * (toUnit A ≫ D.c α)
      exact mul_comm _ _
    intro U _ hh
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_four, Sum.elim_inl, Sum.elim_inr,
      DegPre.famφB, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, e₁, e₂]
    simp only [_root_.mul_assoc]; rfl
  obtain ⟨σ, hσ⟩ := exists_sec D.P.isLB hF s₁
  refine ⟨σ, ?_⟩
  set xx := (snd T A).left z
  choose J hJ using fun χ : A.left ⟶ A.left => exists_chart D.P.isLB (χ xx)
  obtain ⟨(k : Fin 2 → D.P.L.ι), hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  have hv : IsUnit (sval s (𝟙 A.left ≫ iota) xx J) := by
    refine H1.SectionArithmetic.isUnit_sval s (𝟙 A.left ≫ iota) xx hJ k ?_
    rw [Category.id_comp, hiota]; exact hk
  have hval : IsUnit (sval σ (𝟙 A.left) xx J) := by
    rw [hσ _ _ xx J hJ, sval_pullMulSec s iota u hu (𝟙 A.left) xx hJ]
    exact hv.mul (Units.isUnit _)
  have hm := (Good.mem hJ (D.famφB α) (𝟙 A.left))
  rw [sval] at hval
  erw [gs_eq (𝟙 A.left) xx _ hm] at hval
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun k => J (𝟙 A.left ≫ D.famφB α k), ?_⟩
  exact (A.left.mem_basicOpen _ xx hm).2 hval

theorem exists_sec_nonzeroLocus_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R],
    IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (D : DegPre R) (α : D.X) (x : D.P.A.left),
    D.P.A.hom x = IsLocalRing.closedPoint R → ∃ σ : D.SecB 2 α, x ∈ nonzeroLocus σ := by
  intro R _ _ _ _ _ D α x hx
  let S := Spec (CommRingCat.of R)
  let tk : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ S :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let T : Over S := 𝟙_ (Over S)
  let ρ : Over.mk (tk ≫ T.hom) ⟶ Over.mk T.hom := Over.homMk tk rfl
  obtain ⟨y, hy⟩ : ∃ y : (Over.mk (tk ≫ T.hom) ⊗ D.P.A).left, (snd _ D.P.A).left y = x := by
    obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of (IsLocalRing.ResidueField R))) := inferInstance
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := tk ≫ T.hom) (g := D.P.A.hom) p x (by
      rw [hx]; exact IsLocalRing.PrimeSpectrum.comap_residue R p)
    exact ⟨z, hz⟩
  have hg := GlobalTheory.T.exists_section_translateTensor_fibre_nonvanishing S D.P _ (tk ≫ T.hom) (ρ ≫ D.c α) y
  rw [← whisker_eq_twistLB] at hg
  obtain ⟨sb, hsb⟩ := hg
  obtain ⟨s, hs⟩ := (GlobalTheory.abelianSchemeLaws_all.2.secTwist S D.P 2 (by norm_num) R T.hom (D.c α)).2 sb
  have hz := mem_of_isPullSecLC D.P.L _ _ _ s sb hs y hsb
  obtain ⟨σ, hσ⟩ := transfer D α s _ hz
  refine ⟨σ, ?_⟩
  have e : (snd T D.P.A).left ((ρ ▷ D.P.A).left y) = x := by
    rw [← hy]
    have e' := congrArg (fun f => f.left.base y) (whiskerRight_snd ρ D.P.A)
    exact e'
  rwa [e] at hσ

end GlobalTheory.TwistGen
end
end
end
