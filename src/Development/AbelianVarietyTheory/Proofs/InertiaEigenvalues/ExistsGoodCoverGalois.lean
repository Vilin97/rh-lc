module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPinsStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeEmbeddingLiftDatumHermitianSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMemberDictionaryContextGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDictionaryCharacterLaws
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryInvariantRationalLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OnbPerp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformisedLevelCoverExistsConstantsDominantWeigStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevelStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelMulSplit
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelCoverUniformisationDictionary

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverUnif



theorem exists_unf_dict : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ,
    GoodEmb T.Q.c σ → ∀ (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F) (d : DeltaDat (T.Q.Xo j) c' 0) (σ₂ : d.c₂.F →+* ℂ),
    d.IsLev → d.l₂.A = 1 → σ₂.comp ((d.eF : c'.F →+* d.c₂.F).comp (incF T.Q.c c' hle)) = σ →
    ∃ (U₂ : Unf d.Xo₂ d.c₂ σ₂ D.R.r) (dict₂ : GA D (T.V j σ) → Σ k, Frame (U₂.X k).Ψ D.R.r),
      ∀ cc₂, (⟨c', hle, d, σ₂, U₂, dict₂, cc₂⟩ : Cover T j σ).IsUnif := by
  intro D T hT j hj σ hσ c' hle d σ₂ hlev hA hinc
  obtain ⟨hr, -⟩ := hT.modelW j hj σ hσ
  obtain ⟨hio, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT j hj σ hσ _ rfl hr
  have hpq := (exists_iotaOK D T.Q hT.pins j hj).2
  have hpos : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  have hg₂ : GoodEmb d.c₂ σ₂ := by
    have h1 := hσ
    rw [← hinc] at h1
    exact h1
  obtain ⟨C, hC, hCι, hCx⟩ := (exists_ctx D T.Q.H (T.Q.Dw j) d.l₂ d.Xo₂ d.c₂ σ₂ (T.V j σ) D.R.r hr _ hio hpos hA
    hg₂).2.2 (T.x₀ j σ) hx₀
  obtain ⟨Kf, hKf⟩ := (PrincLevel.exists_levelK_and_nhds D (T.V j σ) d.l₂.M).1
  obtain ⟨un, dict, mu, hdict, -, hP⟩ := exists_pkgLaws D _ _ _ _ _ _ _ _ C hC Kf hKf 1
    ⟨continuous_const, fun _ => rfl⟩ (fun _ => rfl)
  obtain ⟨g, e, F, ik, φ, th, hth, -, hdl⟩ := hP.dictLaws
  have hdom := (dict_invariant D _ _ _ _ _ _ _ _ C hC dict hdict Kf hKf).2.2.1
  refine ⟨C.unf un, dict, fun cc₂ => ⟨hlev, hA, hinc, hP.unf, hdom, hr, g, e, F, ik, φ, th, hP.modelW, hth, ?_⟩⟩
  rw [← hCι, ← hCx]
  exact hdl

end GlobalTheory.CoverUnif
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelCoverUniformisationDictionaryStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_levelCover_uniformisation_dictionary : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F) (d : DeltaDat (T.Q.Xo j) c' 0) (σ₂ : d.c₂.F →+* ℂ), d.IsLev → d.l₂.A = 1 → σ₂.comp ((d.eF : c'.F →+* d.c₂.F).comp (incF T.Q.c c' hle)) = σ → ∃ (U₂ : Unf d.Xo₂ d.c₂ σ₂ D.R.r) (dict₂ : GA D (T.V j σ) → Σ k, Frame (U₂.X k).Ψ D.R.r), ∀ cc₂, (⟨c', hle, d, σ₂, U₂, dict₂, cc₂⟩ : Cover T j σ).IsUnif := by
  first | exact @GlobalTheory.CoverUnif.exists_unf_dict | exact GlobalTheory.CoverUnif.exists_unf_dict | (intros; apply GlobalTheory.CoverUnif.exists_unf_dict <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalZeta

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

set_option autoImplicit false

namespace GlobalTheory.CoverExists

theorem exists_ext_of_le {K L : IntermediateField ℚ ℂ} [FiniteDimensional ℚ L] (hle : K ≤ L) (σ : K →+* ℂ) :
    ∃ σ' : L →+* ℂ, σ'.comp (IntermediateField.inclusion hle).toRingHom = σ := by
  letI : Algebra K L := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  letI : Algebra K ℂ := σ.toAlgebra
  haveI : IsScalarTower ℚ K L :=
    IsScalarTower.of_algebraMap_eq (fun x => ((IntermediateField.inclusion hle).commutes x).symm)
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  refine ⟨(IsAlgClosed.lift : L →ₐ[K] ℂ).toRingHom, ?_⟩
  ext x
  exact (IsAlgClosed.lift : L →ₐ[K] ℂ).commutes x

end GlobalTheory.CoverExists

namespace GlobalTheory.CoverExists

end GlobalTheory.CoverExists
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverGalois

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverGalois

theorem fieldRange_of_normal (L : IntermediateField ℚ ℂ) [hN : Normal ℚ L] (f : L →+* ℂ) :
    f.toRatAlgHom.fieldRange = L :=
  @AlgHom.fieldRange_of_normal ℚ ℂ _ _ _ L (by convert hN) f.toRatAlgHom

theorem exists_goodCover_galois (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (hJ : LawsJ T) (i : Fin D.R.m) (hj : InR D ((i : ℕ) + 1)) (n pd : ℕ) (I : Ideal (𝓞 D.host.E))
    (haux : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.IsAuxiliarySplitSquarefreeLevel D T.Q.l.M pd)
    (hK : I = Ideal.span {x | x ∈ I ∧ x ∈ Algebra.adjoin ℤ {T.Q.H.w0}})
    (hprod : I * I.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = Ideal.span {(pd : 𝓞 D.host.E)})
    (hsup : I ⊔ I.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤)
    (L : IntermediateField ℚ ℂ) [FiniteDimensional ℚ L] [Normal ℚ L] (hle : T.Q.c.F ≤ L)
    (hz : zeta (T.Q.l.M * pd) ∈ L) (hsm : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SmallIn R i (L.val : L →+* ℂ))
    (hray : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (T.Q.l.M * pd) L.toSubfield) :
    ∃ C : Cover T ((i : ℕ) + 1) T.σ₀, C.d.pd = pd ∧ C.d.I = I ∧ C.σ₂.fieldRange = L.toSubfield ∧
      GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.GoodCover T R i C n := by
  have hσ : GoodEmb T.Q.c T.σ₀ := T.toCore.good_σ₀
  obtain ⟨hodd, -, -, hcop, -⟩ := id haux
  have hnum := GlobalTheory.T.numerical_consequences_of_pins D T.Q hJ.toLawsM.pins
  have hA : T.Q.l.A = 1 := hnum.2.1
  have hpq : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by
    have := hnum.2.2.2.2.2.2 _ hj; omega
  obtain ⟨l₂, hd, hM, hMb, hA₂⟩ := (GlobalTheory.exists_level_mul_split _ T.Q.H T.Q.l).1 pd I hodd hcop hK hprod hsup
  obtain ⟨Xo₂⟩ := GlobalTheory.T.exists_moduli_scheme_polarized_abelian_level _ T.Q.H (T.Q.Dw ((i : ℕ) + 1)) l₂ hpq
  let c' : Coeff T.Q.l :=
    { F := L, fin := inferInstance, conj := fun τ a => hle (T.Q.c.conj τ a)
      zeta_mem := hle T.Q.c.zeta_mem, le := T.Q.c.le.trans hle }
  have hM' : l₂.M' = T.Q.l.M * pd := by
    rw [Level.M', hA₂, hA, hM, Nat.lcm_one_right]
  let c₂ : Coeff l₂ :=
    { F := c'.F, fin := c'.fin, conj := c'.conj
      zeta_mem := by rw [hM']; exact hz
      le := by have h := c'.le; unfold KA at h ⊢; rw [hA₂]; exact h }
  obtain ⟨d, hdpd, hdI, hdl, -, -, -, hlev, -⟩ := GlobalTheory.LevelCover.exists_deltaDat_isLev _ T.Q.H (T.Q.Dw ((i : ℕ) + 1)) T.Q.l
    (T.Q.Xo ((i : ℕ) + 1)) c' hpq 0 pd I l₂ Xo₂ c₂ rfl hd hM hcop hMb hsup
  obtain ⟨σ', hσ'⟩ := GlobalTheory.CoverExists.exists_ext_of_le (K := T.Q.c.F) (L := L) hle T.σ₀
  let σ₂ : d.c₂.F →+* ℂ := σ'.comp (d.eF.symm : d.c₂.F →+* c'.F)
  have hσ₂ : σ₂.comp ((d.eF : c'.F →+* d.c₂.F).comp (incF T.Q.c c' hle)) = T.σ₀ := by
    rw [← hσ']; ext x; simp [σ₂, incF]
  have hA1 : d.l₂.A = 1 := by rw [hdl, hA₂, hA]
  obtain ⟨U₂, dict₂, hU⟩ := GlobalTheory.T.exists_levelCover_uniformisation_dictionary D T hJ _ hj T.σ₀ hσ c' hle d σ₂ hlev hA1 hσ₂

  have hrange : (σ'.toRatAlgHom).fieldRange = L := fieldRange_of_normal L σ'
  have hsurj : ∀ y : L, ∃ z : d.c₂.F, σ₂ z = (y : ℂ) := by
    intro y
    have hy : (y : ℂ) ∈ (σ'.toRatAlgHom).fieldRange := by rw [hrange]; exact y.2
    obtain ⟨x, hx⟩ := AlgHom.mem_fieldRange.1 hy
    exact ⟨d.eF x, by simp [σ₂, ← hx]⟩
  have hfr : σ₂.fieldRange = L.toSubfield := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      have : σ' (d.eF.symm z) ∈ (σ'.toRatAlgHom).fieldRange := AlgHom.mem_fieldRange.2 ⟨_, rfl⟩
      rw [hrange] at this
      exact this
    · intro hx
      obtain ⟨z, hz'⟩ := hsurj ⟨x, hx⟩
      exact ⟨z, hz'⟩
  have hsm₂ : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SmallIn R i σ₂ := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨y, hy⟩ := hsm.1 v hv
      obtain ⟨z, hz'⟩ := hsurj y
      exact ⟨z, hz'.trans hy⟩
    · obtain ⟨y, hy⟩ := hsm.2 v hv
      obtain ⟨z, hz'⟩ := hsurj y
      exact ⟨z, hz'.trans hy⟩
  let C₀ : Cover T ((i : ℕ) + 1) T.σ₀ := ⟨c', hle, d, σ₂, U₂, dict₂, fun _ => 1⟩
  have hdom : ∀ m, Even m → Dom (0 : (D.host.E →+* ℂ) × ℕ → ℕ) m := fun m hm =>
    ⟨fun _ _ _ _ => le_rfl, hm⟩
  have hauxd : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.IsAuxiliarySplitSquarefreeLevel D T.Q.l.M d.pd := hdpd ▸ haux
  by_cases hn : Even n
  · obtain ⟨cc₂, hcc⟩ := GlobalTheory.T.uniformisedLevelCover_exists_constants_dominantWeights D T hJ _ hj T.σ₀ hσ C₀ (hU _) n
    refine ⟨⟨c', hle, d, σ₂, U₂, dict₂, cc₂⟩, hdpd, hdI, hfr, hU cc₂, hcc, hauxd, hsm₂, ?_⟩
    show GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (T.Q.l.M * d.pd) σ₂.fieldRange
    rw [hfr, hdpd]; exact hray
  · obtain ⟨cc₂, hcc⟩ := GlobalTheory.T.uniformisedLevelCover_exists_constants_dominantWeights D T hJ _ hj T.σ₀ hσ C₀ (hU _) 0
    refine ⟨⟨c', hle, d, σ₂, U₂, dict₂, cc₂⟩, hdpd, hdI, hfr, hU cc₂, fun a ha => absurd ha.2 hn, hauxd, hsm₂, ?_⟩
    show GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (T.Q.l.M * d.pd) σ₂.fieldRange
    rw [hfr, hdpd]; exact hray

end GlobalTheory.CoverGalois
end
end
end
