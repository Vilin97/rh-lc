module

public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ConclusionsAtIdentity
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasisStatement
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermitianMetricDifferentialEqOfPairingRelationStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralTangentVectorCoordinates
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegersStatement
import Mathlib.RingTheory.RegularLocalRing.Defs
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNormalisedPolarisation
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LbIsoCubeLBMulRightOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LinearIndependentOfIsLieBasis
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyPolAVGenericFibreWithLieBasis

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFamIsometryInjective

section

@[expose] public section

open NumberField ReciprocityTheory.GeometryOfNumbersTheory
open scoped ComplexOrder

namespace GlobalTheory.LamF

theorem hermFam_isometry_injective {K : Type*} [Field K] [NumberField K] {V V' : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    (h : HermFam K V) (h' : HermFam K V') (M : V →ₗ[K] V')
    (hM : ∀ s a b, h'.form s (M a) (M b) = h.form s a b) : Function.Injective M := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  obtain ⟨s⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hli : LinearIndependent K ![x] := by
    rw [linearIndependent_unique_iff]; simpa using h0
  have h1 := (h.posDef s 1 ![x] hli).diag_pos (i := 0)
  have h2 : h'.form s (M x) (M x) = 0 := by
    have := h'.smul_right s 0 (M x) (M x)
    rw [zero_smul, map_zero, zero_mul] at this
    rw [← this, hx]
  rw [hM] at h2
  simp [h2] at h1

theorem deg_map_isometry : ∀ (K : Type) [Field K] [NumberField K] (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : HermFam K V) (h' : HermFam K V') (M : V →ₗ[K] V') (Λ : Submodule (𝓞 K) V), Λ.FG → (∀ s a b, h'.form s (M a) (M b) = h.form s a b) → ReciprocityTheory.GeometryOfNumbersTheory.deg h' (Λ.map (M.restrictScalars (𝓞 K))) = ReciprocityTheory.GeometryOfNumbersTheory.deg h Λ := by
  intro K _ _ V V' _ _ _ _ _ _ _ _ h h' M E hE hM
  have hinj := hermFam_isometry_injective h h' M hM
  obtain ⟨v, hv⟩ := exists_isFrame E hE
  have hv' : IsFrame K (E.map (M.restrictScalars (𝓞 K))) (M ∘ v) := by
    refine ⟨fun i => ⟨v i, hv.1 i, rfl⟩, hv.2.1.map' M (LinearMap.ker_eq_bot.2 hinj), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [Set.range_comp, Submodule.span_image]
    exact ⟨x, hv.2.2 hx, rfl⟩
  rw [arakelovDegree_eq_degreeOfFamily h hE hv, arakelovDegree_eq_degreeOfFamily h' (hE.map _) hv']
  unfold degreeOfFamily
  have e1 : ∀ s, h'.gram s (M ∘ v) = h.gram s v := fun s => by
    ext i j; simp [HermFam.gram, hM]
  have e2 : Submodule.span (𝓞 K) (Set.range (M ∘ v)) =
      (Submodule.span (𝓞 K) (Set.range v)).map (M.restrictScalars (𝓞 K)) := by
    rw [Submodule.map_span, Set.range_comp]; rfl
  simp only [e1, e2, Submodule.map_toAddSubgroup]
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ (by exact hinj)]

end GlobalTheory.LamF
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegEigLatEqOfIso

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section
namespace GlobalTheory.LamF


open IntCoord in
theorem diff_mem_eigLat {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} {F : GenFib P}
    {F' : GenFib P'} {O : Type} [CommRing O] {a : OAct O P.A} {a' : OAct O P'.A} {f : P.A ⟶ P'.A}
    (hf : ∀ x, a.act x ≫ f = f ≫ a'.act x) {M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)}
    (hM : F.IsDiffOf F' f M) (τ : O →+* 𝓞 K) {c : Fin F.P₀.g → K} (hc : c ∈ F.eigLat a τ) :
    M c ∈ F'.eigLat a' τ := by
  obtain ⟨u, hu, he⟩ := ((integral_tangent_coordinates K P F).2.2.2.2.2 O a τ c).1 hc
  refine Submodule.subset_span ⟨u ≫ f, hM u c hu, fun x => ?_⟩
  rw [isLieComb_one_iff, Category.assoc, ← hf, ← Category.assoc, (isLieComb_one_iff _ _ _).1 (he x),
    Category.assoc]

theorem map_eigLat_of_iso {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} {F : GenFib P}
    {F' : GenFib P'} {O : Type} [CommRing O] {a : OAct O P.A} {a' : OAct O P'.A} (e : P.A ≅ P'.A)
    (hf : ∀ x, a.act x ≫ e.hom = e.hom ≫ a'.act x) {M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)}
    {M' : (Fin F'.P₀.g → K) →ₗ[K] (Fin F.P₀.g → K)}
    (hM : F.IsDiffOf F' e.hom M) (hM' : F'.IsDiffOf F e.inv M') (τ : O →+* 𝓞 K) :
    (F.eigLat a τ).map (M.restrictScalars (𝓞 K)) = F'.eigLat a' τ := by
  refine le_antisymm ?_ fun c hc => ?_
  · rintro _ ⟨c, hc, rfl⟩
    exact diff_mem_eigLat hf hM τ hc
  · have hf' : ∀ x, a'.act x ≫ e.inv = e.inv ≫ a.act x := fun x => by
      rw [Iso.comp_inv_eq, Category.assoc, hf, Iso.inv_hom_id_assoc]
    refine ⟨M' c, diff_mem_eigLat hf' hM' τ hc, ?_⟩
    obtain ⟨u, hu, -⟩ := ((integral_tangent_coordinates K P' F').2.2.2.2.2 O a' τ c).1 hc
    have h2 := hM _ _ (hM' _ _ hu)
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h2
    exact ((integral_tangent_coordinates K P' F').1 u hu.1).unique h2 hu

theorem deg_eigLat_eq_of_iso : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P P' : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (F' : GenFib P') (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)) (O : Type) [CommRing O] (a : OAct O P.A) (a' : OAct O P'.A) (e : P.A ≅ P'.A), F.IsHerm h → F'.IsHerm h' → Serre.IsLinearHom a a' e.hom → LamEq P'.L e.hom e.hom P.L (𝟙 P.A) (𝟙 P.A) → ∀ τ : O →+* 𝓞 K, deg h (F.eigLat a τ) = deg h' (F'.eigLat a' τ) := by
  intro hT hL K _ _ P P' F F' h h' O _ a a' e hh hh' hlin hlam τ
  have hm : IsMonHom e.hom := hlin.1
  have hm' : IsMonHom e.inv := inferInstance
  obtain ⟨M, hM, -⟩ := (GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P' F' e.hom hm).1
  obtain ⟨M', hM', -⟩ := (GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P' F' P F e.inv hm').1
  have hid : F.IsDiffOf F (𝟙 P.A) LinearMap.id := fun u c hu => by simpa using hu
  have hiso := GlobalTheory.T.hermitianMetric_differential_eq_of_pairing_relation hT hL K P F P' F' h h' e.hom (𝟙 P.A) M LinearMap.id hh hh' hm inferInstance hlam hM hid
  have hle : F.eigLat a τ ≤ F.lieLat := Submodule.span_mono fun c ⟨u, hu, _⟩ => ⟨u, hu⟩
  have hfg : (F.eigLat a τ).FG := (GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K P F).1.of_le hle
  rw [← map_eigLat_of_iso e hlin.2 hM hM' τ]
  exact (deg_map_isometry K _ _ h h' M _ hfg hiso).symm

end GlobalTheory.LamF
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPatOfPolAV

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section

namespace GlobalTheory.LamF

theorem exists_pat_of_polAV : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (act : OAct (𝓞 E) P.A), (∀ a, LamEq P.L (act.act a) (𝟙 P.A) P.L (𝟙 P.A) (act.act (H.bar a))) → ∃ (T : PAT H (Sp R)) (e : T.t.G ≅ P.A), T.g = P.g ∧ Serre.IsLinearHom T.t.act act e.hom ∧ LamEq P.L e.hom e.hom T.t.PP.L (𝟙 T.t.G) (𝟙 T.t.G) := by
  intro laws E _ _ _ H R _ _ P act hadj
  have : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨L', hL', ⟨rig, hrig⟩, hsym, hamp, hk, hlam, prim⟩ :=
    exists_normalised_polarisation laws R P (act.act H.w0) (act.act (H.bar H.w0)) (act.hom _) (act.hom _)
      (by rw [← act.add, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel, act.one]) (hadj H.w0)
  let PP : RigLB P.A := ⟨L', rig, hL', hrig⟩
  let P' : Out.PolAV (Sp R) :=
    { A := P.A, isAb := P.isAb, g := P.g, smoothDim := P.smoothDim, L := L', isLB := hL', rigid := ⟨rig, hrig⟩,
      sym := hsym, ample := hamp, ktriv := hk }
  obtain ⟨cub⟩ := (laws.cube _ P' PP rfl).1
  have sym : PP.IsSymmetric :=
    GlobalTheory.PrimNorm.isSymmetric_of_hasGen PP (exists_gen_neg_of_sym laws.globalFns P.isAb hL' hsym)
  have lb : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ P.A)) {L : LB P.A.left}, L.IsLB → (cubeLB P.A x L).IsLB :=
    fun x L hL => DVR.linComb_isLB _ hL _ _
  have pts := ((GlobalTheory.LamCalc.lamEq_calculus _ P.A P.A P.A P.A P.A L' P.L P.L hL' P.isLB P.isLB
    (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)).2.1 hlam).2.2.2.2
  simp only [Category.comp_id] at pts
  have adj : ∀ a, LBIso (cubeLB P.A ![fst P.A P.A ≫ act.act a, snd P.A P.A] L')
      (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ act.act (H.bar a)] L') := fun a =>
    LBIso.trans (lb _ hL') (lb _ P.isLB) (lb _ hL') (pts _ _ _)
      (LBIso.trans (lb _ P.isLB) (lb _ P.isLB) (lb _ hL')
        (by simpa only [LamEq, Category.comp_id] using hadj a) (pts _ _ _).symm)
  exact ⟨{ t := { G := P.A, semi := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ P.isAb, act := act, PP := PP, cub := cub,
                  sym := sym, adj := adj, prim := prim },
           ab := P.isAb, g := P.g, dim := P.smoothDim, sym := hsym, ample := hamp, ktriv := hk },
    Iso.refl _, rfl, Serre.IsLinearHom.id act, LBIso.symm hlam⟩

end GlobalTheory.LamF
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HasTypeOfIso

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.CM

theorem hasType_of_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (G G' : Over (Sp R)) [GrpObj G] [GrpObj G'] (a : OAct (𝓞 E) G) (a' : OAct (𝓞 E) G') (e : G ≅ G') (ρ : R) (p q : ℕ), Serre.IsLinearHom a a' e.hom → HasType H a' ρ p q → HasType H a ρ p q := by
  intro E _ _ _ H R _ G G' _ _ a a' e ρ p q he h k _ _ β hβ τ
  have := he.isMonHom
  have key : ∀ n, LieMult a (spMap β) τ n ↔ LieMult a' (spMap β) τ n := fun n => by
    have := LiePull.lieMult_pull _ _ _ G' G (𝟙 _) e.hom.left a' a (isGrpPullback_of_iso e)
      (fun c => congrArg (fun z => z.left) (he.comm c)) k (spMap β) τ n
    rwa [Category.comp_id] at this
  rw [key, key]
  exact h k β hβ τ

end GlobalTheory.CM
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TwoMulDegEigenLatticePolarizedAbelianScheme

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem two_mul_deg_eigLat_of_polAV : DegSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (P : Out.PolAV (Sp (𝓞 K))) (act : OAct (𝓞 E) P.A), (∀ a, LamEq P.L (act.act a) (𝟙 P.A) P.L (𝟙 P.A) (act.act (H.bar a))) → Splits E K → ρ ^ 2 = -(H.d : 𝓞 K) → HasType H act ρ 1 0 → ∀ (F : GenFib P) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ((2 * deg h (F.eigLat act τ) : ℝ) : ℂ) = logOm E χ := by
  intro hD hT hL E _ _ _ H _ χ hχ K _ _ ρ P act hbal hs hρ ht F h hh τ hτ
  obtain ⟨T, e, -, hlin, hlam⟩ := exists_pat_of_polAV hL E H (𝓞 K) P act hbal
  obtain ⟨F₁⟩ := GenFib.nonempty_of_baseChange hL.polBaseChange K T.pol
  obtain ⟨h₁, hh₁⟩ := (LieMetric.exists_unique_isHerm hT hL K T.pol F₁).1
  have ht₁ : HasType H T.t.act ρ 1 0 := hasType_of_iso E H (𝓞 K) _ _ _ _ e ρ 1 0 hlin ht
  rw [← deg_eigLat_eq_of_iso hT hL K T.pol P F₁ F h₁ h (𝓞 E) T.t.act act e hh₁ hh hlin hlam τ]
  exact hD E H χ hχ K ρ T hs hρ ht₁ F₁ h₁ hh₁ τ hτ

end GlobalTheory.LamF
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TwoMulDegEigenLatticePolarizedAbelianSchemeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.two_mul_deg_eigenLattice_polarizedAbelianScheme : DegSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (P : Out.PolAV (Sp (𝓞 K))) (act : OAct (𝓞 E) P.A), (∀ a, LamEq P.L (act.act a) (𝟙 P.A) P.L (𝟙 P.A) (act.act (H.bar a))) → Splits E K → ρ ^ 2 = -(H.d : 𝓞 K) → HasType H act ρ 1 0 → ∀ (F : GenFib P) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ((2 * deg h (F.eigLat act τ) : ℝ) : ℂ) = logOm E χ := by
  first | exact @GlobalTheory.LamF.two_mul_deg_eigLat_of_polAV | exact GlobalTheory.LamF.two_mul_deg_eigLat_of_polAV | (intros; apply GlobalTheory.LamF.two_mul_deg_eigLat_of_polAV <;> assumption)
end
end
