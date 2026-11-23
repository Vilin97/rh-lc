module

public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Statements
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PAENeighbourhoods
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PAETopologicalRing
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PClosureIsSubmonoid
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PEDenseInAE
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PEichlerAtPlace
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PEichlerDense
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PHypPairExists
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.LocGen
public import Mathlib.RingTheory.Flat.Basic
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PLocalRingHypotheses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.EichPreserves
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PPlaceMaps
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PTruncation

-- Source module: GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PLocalInClosure

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA

theorem LocalInClosure.proof (hHP : HypPairExists.Statement) (hCl : ClosureIsSubmonoid.Statement)
    (hLR : LocalRingHypotheses.Statement) (hPM : PlaceMaps.Statement)
    (hEA : EichlerAtPlace.Statement) : LocalInClosure.Statement := by
  intro F E _ _ _ _ _ c hrk hc N J hJ hdet ⟨e, he0, hee⟩ _ _ v g hg
  obtain ⟨hinv, hfix, hrank2, hred, h2, hcomm, hform⟩ := hLR F E c hrk hc v

  have hinj : Function.Injective (inclV E v) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F (v.adicCompletion F)).injective
  have hcinv : ∀ x, c.toRingHom (c.toRingHom x) = x := fun x =>
    hinj (by
      change inclV E v (c (c x)) = inclV E v x
      rw [← hcomm, ← hcomm, hinv])

  obtain ⟨f, hff, hef⟩ := hHP E c.toRingHom hcinv two_ne_zero N J hJ hdet e he0 hee
  obtain ⟨-, h1, hmul, heich⟩ := hCl F E c hrk hc N J hJ hdet e f hee hff hef

  have hJv : (J.map (inclV E v))ᵀ = (J.map (inclV E v)).map (sigV c v) := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply]
    rw [hcomm]
    have h := Matrix.ext_iff.mpr hJ i j
    simp only [Matrix.transpose_apply, Matrix.map_apply] at h
    rw [h]
  have hdetv : IsUnit (J.map (inclV E v)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hdet.map _
  have hzero : ∀ x y : Fin N → E, hf c.toRingHom J x y = 0 →
      hf (sigV c v).toRingHom (J.map (inclV E v)) (inclV E v ∘ x) (inclV E v ∘ y) = 0 :=
    fun x y h => by rw [← hform, h, map_zero]
  have hefv : hf (sigV c v).toRingHom (J.map (inclV E v)) (inclV E v ∘ e) (inclV E v ∘ f) = 1 := by
    rw [← hform, hef, map_one]
  have hg' := hg
  rw [locGen _ _ (sigV c v) hinv hfix hrank2 hred h2 N _ hJv hdetv _ _ (hzero e e hee)
    (hzero f f hff) hefv] at hg'
  clear hg

  obtain ⟨-, hPv⟩ := hPM F E c hrk hc
  obtain ⟨-, -, -, -, -, -, -, -, hPN⟩ := hPv v
  obtain ⟨hemb1, hembmul, -⟩ := hPN N
  induction hg' using Submonoid.closure_induction with
  | mem x hx => exact heich ((hEA F E c hrk hc v N J).2 hJ e f hee hff hef x hx)
  | one => rw [hemb1]; exact h1
  | mul x y _ _ hx hy => rw [hembmul]; exact hmul _ hx _ hy

end StrongApprox

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.StrongApproximation.POrthProjection

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem sigA_inclA_apply {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E)
    (x : E) : sigA c (inclA F E x) = inclA F E (c x) := by
  simp [sigA, inclA, Algebra.TensorProduct.map_tmul]

theorem OrthProjection.proof (hT : AETopologicalRing.Statement) : OrthProjection.Statement := by
  refine ⟨?_, ?_⟩
  · intro R _ σ hσ N J hJ e f hee hff hef
    have hfe : hf σ J f e = 1 := by rw [← hf_symm hσ hJ, hef, map_one]
    have perp : ∀ u, hf σ J (perpProj σ J e f u) e = 0 ∧ hf σ J (perpProj σ J e f u) f = 0 := by
      intro u
      simp only [perpProj, hf_sub_left, hf_smul_left, hee, hff, hef, hfe]
      constructor <;> ring
    have fix : ∀ u, hf σ J u e = 0 → hf σ J u f = 0 → perpProj σ J e f u = u := by
      intro u h1 h2
      simp [perpProj, h1, h2]
    refine ⟨⟨fun u v => ?_, fun a u => ?_⟩, fun u => fix _ (perp u).1 (perp u).2, perp, fix⟩
    · simp only [perpProj, hf_add_left, add_smul]
      abel
    · simp only [perpProj, hf_smul_left, smul_sub, mul_smul]
  · intro F E _ _ _ _ _ c h2 hc N J e f _ _
    have := (hT F E c h2 hc).1
    refine ⟨?_, fun u => ?_⟩
    · unfold perpProj hf
      fun_prop
    · have hmap : ∀ x y : Fin N → E, inclA F E (hf c.toRingHom J x y) =
          hf (sigA c) (J.map (inclA F E)) (inclA F E ∘ x) (inclA F E ∘ y) := by
        intro x y

        simp [hf, map_sum, map_mul, sigA_inclA_apply]
      funext i
      simp only [perpProj, Function.comp_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub,
        map_mul, hmap]

end GroundTheory.Heights₂.Heights.StrongApprox
end
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PSAHolds

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem SAHolds.of_neighbourhoods_truncation (hNb : AENeighbourhoods.Statement)
    (hTr : Truncation.Statement) : SAHolds.Statement := by
  classical
  intro F E _ _ _ _ _ c hrk hc N J hJ hdet hiso _ _ x hx
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AE F E)
  obtain ⟨hN1, hN2⟩ := hNb F E c hrk hc
  change x ∈ Cl c J
  rw [Cl, ← closure_closure, mem_closure_iff_nhds]
  intro U hU
  have hU' : (fun M => x + M) ⁻¹' U ∈ 𝓝 (0 : Matrix (Fin N) (Fin N) (AE F E)) := by
    have hcont : Continuous (fun M : Matrix (Fin N) (Fin N) (AE F E) => x + M) :=
      continuous_const.add continuous_id
    apply hcont.continuousAt.preimage_mem_nhds
    simpa using hU
  obtain ⟨S₀, hS₀⟩ := hN1 N _ hU'
  choose T hT using fun p : Fin N × Fin N => hN2 (x p.1 p.2)
  set S : Finset (HeightOneSpectrum (𝓞 F)) := S₀ ∪ Finset.univ.biUnion T with hSdef
  obtain ⟨t1, t2, -, t4⟩ := hTr F E c hrk hc N J hJ hdet hiso S x
  refine ⟨trunc E S x, ?_, t4 hx⟩
  have hmem : x + (trunc E S x - x) ∈ U := by
    apply hS₀
    intro i j
    have hS : ∀ v ∈ S, compAt E v ((trunc E S x - x) i j) = 0 := by
      intro v hv
      have h := congrFun (congrFun (t1 v hv) i) j
      simp only [Matrix.map_apply] at h
      rw [Matrix.sub_apply, map_sub, h, sub_self]
    refine ⟨fun v hv => hS v (Finset.mem_union_left _ hv), fun v hv => ?_⟩
    by_cases hvS : v ∈ S
    · rw [hS v hvS]; exact zero_mem _
    · have h := congrFun (congrFun (t2 v hvS) i) j
      simp only [Matrix.map_apply] at h
      have hvT : v ∉ T (i, j) := fun h' =>
        hvS (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _, h'⟩))
      have hx' : compAt E v (x i j) ∈ intAt E v := hT (i, j) v hvT
      rw [Matrix.sub_apply, map_sub, h]
      refine sub_mem ?_ hx'
      rw [Matrix.one_apply]
      split_ifs
      · exact AddSubgroup.subset_closure
          ⟨1, one_mem _, 1, by simp [Algebra.TensorProduct.one_def]⟩
      · exact zero_mem _
  simpa using hmem

theorem SAHolds.proof (_hHyp : HypPairExists.Statement) (hNb : AENeighbourhoods.Statement)
    (hTr : Truncation.Statement) : SAHolds.Statement :=
  SAHolds.of_neighbourhoods_truncation hNb hTr

end StrongApprox

end GroundTheory.Heights₂.Heights
end
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PSAOpenHolds

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem map_inclA_mem_SU {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) {γ : Matrix (Fin N) (Fin N) E}
    (hγ : γ ∈ SU c.toRingHom J) :
    γ.map (inclA F E) ∈ SU (sigA c) (J.map (inclA F E)) := by
  obtain ⟨hdet, hform⟩ := hγ
  have hsig : ∀ y : E, sigA c (inclA F E y) = inclA F E (c y) := by
    intro y
    simp [sigA, inclA, Algebra.TensorProduct.map_tmul]
  have hmap : (γ.map (inclA F E)).map (sigA c) = (γ.map c.toRingHom).map (inclA F E) := by
    ext i j
    simp [hsig]
  refine ⟨?_, ?_⟩
  · rw [show (γ.map (inclA F E)).det = inclA F E γ.det from (RingHom.map_det _ _).symm, hdet, map_one]
  · rw [hmap, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hform]

theorem SAOpenHolds.proof (hSA : SAHolds.Statement) (hTop : AETopologicalRing.Statement) :
    SAOpenHolds.Statement := by
  intro F E _ _ _ _ _ c h2 hc N J hJ hdet hiso _ _ Kg hKsub h1 _ hinv hO x hx
  obtain ⟨O, hOopen, hOK⟩ := hO
  have hxdet : IsUnit x.det := by rw [hx.1]; exact isUnit_one

  have hcont : Continuous (fun g : Matrix (Fin N) (Fin N) (AE F E) => x⁻¹ * g) :=
    ((hTop F E c h2 hc).2.2.2 N (J.map (inclA F E))).1.comp
      (continuous_const.prodMk continuous_id)
  have hUopen : IsOpen ((fun g : Matrix (Fin N) (Fin N) (AE F E) => x⁻¹ * g) ⁻¹' O) :=
    hOopen.preimage hcont
  have h1O : (1 : Matrix (Fin N) (Fin N) (AE F E)) ∈ O := by
    rw [← hOK] at h1; exact h1.1
  have hxU : x ∈ (fun g : Matrix (Fin N) (Fin N) (AE F E) => x⁻¹ * g) ⁻¹' O := by
    change x⁻¹ * x ∈ O
    rw [nonsing_inv_mul x hxdet]; exact h1O
  have hcl := hSA F E c h2 hc N J hJ hdet hiso hx
  obtain ⟨_, hyU, ⟨γ, hγ, rfl⟩⟩ := mem_closure_iff.1 hcl _ hUopen hxU
  have hγA := map_inclA_mem_SU c J hγ
  set k := x⁻¹ * γ.map (inclA F E) with hk
  have hkSU : k ∈ SU (sigA c) (J.map (inclA F E)) :=
    mul_mem_SU (inv_mem_SU _ _ hx) hγA
  have hkK : k ∈ Kg := by rw [← hOK]; exact ⟨hyU, hkSU⟩
  have hkdet : IsUnit k.det := by rw [hkSU.1]; exact isUnit_one
  refine ⟨γ, hγ, k⁻¹, hinv k hkK, ?_⟩
  have hxk : x * k = γ.map (inclA F E) := by
    rw [hk, ← Matrix.mul_assoc, mul_nonsing_inv x hxdet, Matrix.one_mul]
  rw [← hxk, Matrix.mul_assoc, mul_nonsing_inv k hkdet, Matrix.mul_one]

end GroundTheory.Heights₂.Heights.StrongApprox
end
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Assembly

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.StrongApprox

theorem AETopologicalRing.full : AETopologicalRing.Statement := AETopologicalRing.proof

theorem HypPairExists.full : HypPairExists.Statement := HypPairExists.proof

theorem EDenseInAE.full : EDenseInAE.Statement := EDenseInAE.proof AETopologicalRing.full

theorem OrthProjection.full : OrthProjection.Statement := OrthProjection.proof AETopologicalRing.full

theorem EichlerDense.full : EichlerDense.Statement :=
  EichlerDense.proof AETopologicalRing.full EDenseInAE.full OrthProjection.full

theorem ClosureIsSubmonoid.full : ClosureIsSubmonoid.Statement :=
  ClosureIsSubmonoid.proof AETopologicalRing.full EichlerDense.full

theorem LocalRingHypotheses.full : LocalRingHypotheses.Statement := LocalRingHypotheses.proof

theorem PlaceMaps.full : PlaceMaps.Statement := PlaceMaps.proof LocalRingHypotheses.full

theorem EichlerAtPlace.full : EichlerAtPlace.Statement := EichlerAtPlace.proof PlaceMaps.full

theorem LocalInClosure.full : LocalInClosure.Statement :=
  LocalInClosure.proof HypPairExists.full ClosureIsSubmonoid.full LocalRingHypotheses.full
    PlaceMaps.full EichlerAtPlace.full

theorem Truncation.full : Truncation.Statement := Truncation.proof LocalInClosure.full

theorem AENeighbourhoods.full : AENeighbourhoods.Statement :=
  AENeighbourhoods.proof AETopologicalRing.full PlaceMaps.full

theorem SAHolds.full : ReciprocityTheory.ChartRestriction.G.SA.SAStatement :=
  SAHolds.proof HypPairExists.full AENeighbourhoods.full Truncation.full

theorem SAOpenHolds.full : ReciprocityTheory.ChartRestriction.G.SA.SAOpenStatement :=
  SAOpenHolds.proof SAHolds.full AETopologicalRing.full

end GroundTheory.Heights₂.Heights.StrongApprox
end
end
