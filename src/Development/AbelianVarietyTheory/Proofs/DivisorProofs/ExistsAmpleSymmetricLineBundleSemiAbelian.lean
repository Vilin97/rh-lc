module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusDescendFlatBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusFlatLocalBaseChangeStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsHasProjectiveDimensionLEOfResidueField
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsPrincipalMapAwayOfHasProjectiveDimensionLE
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNonzeroLocusEqOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfMemChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointsSubsetAbLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusUnitClosedFibreSemiAb

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiAbAffineUnit

theorem exists_affine_nonzeroLocus_unit : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∃ (M₀ : LB G.left) (s₀ : M₀.Sec), M₀.IsLB ∧ IsAffineOpen (nonzeroLocus s₀) ∧ ∃ y₀ ∈ nonzeroLocus s₀, G.hom y₀ = closedPoint R := by
  intro R _ _ _ G _ hG _
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have hR : IsRegularRing R := GlobalTheory.isRegularRing_of_isRegularLocalRing R
  have : IsIntegral G.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : G.left.IsSeparated := ⟨by rw [← terminal.comp_from G.hom]; infer_instance⟩
  have hst : ∀ x : G.left, UniqueFactorizationMonoid (G.left.presheaf.stalk x) := fun x =>
    have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth R G.hom x
    uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      isPrincipal_map_away_of_hasProjectiveDimensionLE _
  have he : (η[G]).left ≫ G.hom = 𝟙 _ := Over.w (η[G])
  set y₀ : G.left := (η[G]).left (closedPoint R) with hy₀
  have hy : G.hom y₀ = closedPoint R := by
    have h2 := Scheme.Hom.comp_apply (η[G]).left G.hom (closedPoint R : (𝟙_ (Over (Sp R))).left)
    rw [he] at h2
    exact h2.symm
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y₀) trivial
  obtain ⟨L, s, hL, hs⟩ := GlobalTheory.SS.exists_nonzeroLocus_eq_of_isAffineOpen G.left hst W hW ⟨_, hyW⟩
  exact ⟨L, s, hL, hs ▸ hW, y₀, hs ▸ hyW, hy⟩

end GlobalTheory.SemiAbAffineUnit
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusUnitClosedFibreSemiAbStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.exists_affine_nonzeroLocus_unit_closedFibre_semiAb : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∃ (M₀ : LB G.left) (s₀ : M₀.Sec), M₀.IsLB ∧ IsAffineOpen (nonzeroLocus s₀) ∧ ∃ y₀ ∈ nonzeroLocus s₀, G.hom y₀ = closedPoint R := by
  first | exact @GlobalTheory.SemiAbAffineUnit.exists_affine_nonzeroLocus_unit | exact GlobalTheory.SemiAbAffineUnit.exists_affine_nonzeroLocus_unit | (intros; apply GlobalTheory.SemiAbAffineUnit.exists_affine_nonzeroLocus_unit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSymmetricLineBundleGrpScheme

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SymAmple

open GlobalTheory.CechPic

theorem exists_isAmpleLB_symm (S : Scheme.{0}) (G : Over S) [GrpObj G] (M₀ : LB G.left) (h₀ : IsAmpleLB M₀) :
    ∃ M : LB G.left, IsAmpleLB M ∧ LBIso (M.pull (GrpObj.inv : G ⟶ G).left) M := by
  set i : G.left ⟶ G.left := (GrpObj.inv : G ⟶ G).left with hi_def
  have hii : i ≫ i = 𝟙 G.left := by
    rw [hi_def, ← Over.comp_left, GrpObj.inv_comp_inv G, Over.id_left]
  have : IsIso i := ⟨⟨i, hii, hii⟩⟩
  have hL := h₀.isLB
  have h₁ : IsAmpleLB (M₀.pull i) := h₀.pull_of_isAffineHom i
  let M : LB G.left := LB.LinComb M₀ (K := Fin 2) ![𝟙 G.left, i] ![1, 1]
  have hM : M.IsLB := LB.isLB_linComb hL _ _
  have hc : cls M hM = cls M₀ hL + GlobalTheory.CechPic.pull i (cls M₀ hL) := by
    rw [cls_linComb hL]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_zsmul, pull_id]
  refine ⟨M, h₀.tensor h₁ hM ?_, ?_⟩
  · have hd₁ := LB.isLB_div hM hL
    have hd₂ := LB.isLB_div hd₁ (pull_isLB hL i)
    refine (cls_eq_zero_iff hd₂).1 ?_
    rw [cls_div hd₁ (pull_isLB hL i), cls_div hM hL, hc, cls_pull hL]
    abel
  · refine (cls_eq_iff (pull_isLB hM i) hM).1 ?_
    rw [cls_pull hM, hc, map_add (f := _), ← pull_comp, hii, pull_id]
    exact add_comm _ _

end GlobalTheory.SymAmple
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSymmetricLineBundleGrpSchemeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.exists_ample_symmetric_lineBundle_grpScheme : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (M₀ : LB G.left), IsAmpleLB M₀ → ∃ M : LB G.left, IsAmpleLB M ∧ LBIso (M.pull (GrpObj.inv : G ⟶ G).left) M := by
  first | exact @GlobalTheory.SymAmple.exists_isAmpleLB_symm | exact GlobalTheory.SymAmple.exists_isAmpleLB_symm | (intros; apply GlobalTheory.SymAmple.exists_isAmpleLB_symm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTheoremOfSquareSemiAbelianGenericAbelian

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SquareGeneric

theorem exists_gen_square :
    ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSemiAbelian G' → IsAbelianScheme ((Over.pullback (jK R')).obj G') → ∀ N : LB G'.left, N.IsLB → ∀ a : 𝟙_ (Over (Sp R')) ⟶ G', ∃ t : LB.Gen (LB.LinComb N (K := Fin 3) ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left] ![1, 1, -2]), t.IsGen := by
  intro R' _ _ _ _ _ G' _ hG hA N hN a
  have := hG.comm
  let j := jK R'
  let πA := pullback.fst G'.hom j
  have hp : IsProper (pullback.snd G'.hom j) := hA.proper
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.RigCube.exists_gen_theta_generic G' hG hp hN
  let c : G' ⟶ G' := toUnit G' ≫ a
  let c' : G' ⟶ G' := toUnit G' ≫ a⁻¹
  let ℓ : G' ⟶ G3 G' := lift (𝟙 G') (lift c c')
  let h : pullback G'.hom j ⟶ pullback (G3 G').hom j :=
    pullback.map _ _ _ _ ℓ.left (𝟙 _) (𝟙 _) (by rw [Category.comp_id, Over.w]) (by simp)
  have hh : h ≫ pullback.fst (G3 G').hom j = πA ≫ ℓ.left := pullback.lift_fst _ _ _
  let t₁ := LB.pullGen (Theta G' N) (fun _ => pullback.fst (G3 G').hom j) (fun _ => 1) t₀ h
  have ht₁ : t₁.IsGen := DVR.pullGen_isGen _ _ _ _ ht₀ _
  obtain ⟨t₂, ht₂⟩ := gen_chartPull (chartPullIn N (thφ G' (x3 G')) thε (h ≫ pullback.fst (G3 G').hom j)) t₁ ht₁
  have hcc : c * c' = 1 := by
    simp only [c, c']
    rw [← MonObj.comp_mul, _root_.mul_inv_cancel, MonObj.comp_one]

  have hconst : ∀ s : 𝟙_ (Over (Sp R')) ⟶ G', ∃ i, ∀ y, (πA ≫ (toUnit G' ≫ s).left) y ∈ N.U i := by
    intro s
    obtain ⟨p₀⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R'))) := inferInstance
    obtain ⟨i, hi⟩ := exists_chart hN ((j ≫ s.left) p₀)
    have e : πA ≫ (toUnit G' ≫ s).left = pullback.snd G'.hom j ≫ j ≫ s.left := by
      have w : (toUnit G').left = G'.hom := (Category.comp_id _).symm.trans (Over.w (toUnit G'))
      rw [Over.comp_left, w, ← Category.assoc, pullback.condition, Category.assoc]
    refine ⟨i, fun y => ?_⟩
    rw [e, Scheme.Hom.comp_apply, Subsingleton.elim ((pullback.snd G'.hom j) y) p₀]
    exact hi
  let s₃ : Fin 3 → (𝟙_ (Over (Sp R')) ⟶ G') := ![a, a⁻¹, η[G']]
  choose i hi using fun k => hconst (s₃ k)
  let φw : Fin 3 → (pullback G'.hom j ⟶ G'.left) := fun k => πA ≫ (toUnit G' ≫ s₃ k).left
  obtain ⟨w, hw⟩ := GlobalTheory.AbSquare.exists_gen_of_mem_chart hN φw ![1, 1, -2] i hi
  let ψ : Fin 3 → (G'.left ⟶ G'.left) := ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left]
  have hF : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FormEq
      (Sum.elim (fun I => (h ≫ pullback.fst (G3 G').hom j) ≫ thφ G' (x3 G') I) φw)
      (Sum.elim (fun I => -thε I) ![1, 1, -2]) (fun k => πA ≫ ψ k) ![1, 1, -2] := by
    intro U _ g
    rw [Fintype.prod_sum_type]
    dsimp only [Sum.elim_inl, Sum.elim_inr]
    simp only [zpow_neg, Finset.prod_inv_distrib]
    have e : ∀ I, (h ≫ pullback.fst (G3 G').hom j) ≫ thφ G' (x3 G') I = πA ≫ (ℓ.left ≫ thφ G' (x3 G') I) :=
      fun I => by rw [hh, Category.assoc]
    have e2 : (∏ I : thK, g ((h ≫ pullback.fst (G3 G').hom j) ≫ thφ G' (x3 G') I) ^ thε I) =
        ∏ I : thK, (fun q => g (πA ≫ q)) ((lift (𝟙 G') (lift c c')).left ≫ thφ G' (x3 G') I) ^ thε I :=
      Finset.prod_congr rfl fun I _ => by rw [e I]
    rw [e2, prod_cub (𝟙 G') c c' (fun q => g (πA ≫ q))]
    rw [show 𝟙 G' * c * c' = 𝟙 G' by rw [_root_.mul_assoc, hcc, _root_.mul_one], hcc]
    have f0 : φw 0 = πA ≫ c.left := rfl
    have f1 : φw 1 = πA ≫ c'.left := rfl
    have f2 : φw 2 = πA ≫ (1 : G' ⟶ G').left := rfl
    have p0 : ψ 0 = (𝟙 G' * c).left := rfl
    have p1 : ψ 1 = (𝟙 G' * c').left := rfl
    have p2 : ψ 2 = Over.Hom.left (𝟙 G') := (Over.id_left _).symm
    rw [Fin.prod_univ_three, Fin.prod_univ_three, f0, f1, f2, p0, p1, p2]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    abel
  obtain ⟨u, hu, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN hF (LB.mulGen N _ _ _ _ (LB.invGen N _ _ t₂) w)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ ht₂) hw)
  obtain ⟨v, hv⟩ := gen_chartPull (chartPullOut N ψ ![1, 1, -2] πA (fun k => πA ≫ ψ k) (fun _ => rfl)) u hu
  exact GlobalTheory.PicGenericInj.exists_gen_of_generic R' G' hG _ (LB.isLB_linComb hN _ _) ⟨v, hv⟩

end GlobalTheory.SquareGeneric
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTheoremOfSquareSemiAbelianGenericAbelianStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.exists_theorem_of_square_semiAbelian_genericAbelian : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSemiAbelian G' → IsAbelianScheme ((Over.pullback (jK R')).obj G') → ∀ N : LB G'.left, N.IsLB → ∀ a : 𝟙_ (Over (Sp R')) ⟶ G', ∃ t : LB.Gen (LB.LinComb N (K := Fin 3) ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left] ![1, 1, -2]), t.IsGen := by
  first | exact @GlobalTheory.SquareGeneric.exists_gen_square | exact GlobalTheory.SquareGeneric.exists_gen_square | (intros; apply GlobalTheory.SquareGeneric.exists_gen_square <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSymmetricLineBundleSemiAbelian

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SymAmple

theorem exists_ample_symmetric : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∃ M : LB G.left, IsAmpleLB M ∧ LBIso (M.pull (GrpObj.inv : G ⟶ G).left) M := by
  intro R _ _ _ G _ hG hab
  obtain ⟨M₀, s₀, hM, ha, hy₀⟩ := GlobalTheory.T.exists_affine_nonzeroLocus_unit_closedFibre_semiAb R G hG hab
  have hpt := GlobalTheory.T.exists_affine_nonzeroLocus_flat_local_baseChange GlobalTheory.T.exists_theorem_of_square_semiAbelian_genericAbelian R G hG hab M₀ hM s₀ ha hy₀
  have := hG.quasiCompact
  have := hG.separated
  have hcs : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have hamp : IsAmpleLB M₀ := ⟨hM, hcs, fun y => by
    obtain ⟨R', _, ρ, hρ, x', hx', hs⟩ := hpt y
    have h := GlobalTheory.T.exists_affine_nonzeroLocus_descend_flat_baseChange R R' ρ hρ G.left G.hom inferInstance inferInstance M₀ hM x' hs
    rwa [hx'] at h⟩
  exact GlobalTheory.T.exists_ample_symmetric_lineBundle_grpScheme (Sp R) G M₀ hamp

end GlobalTheory.SymAmple
end
end
