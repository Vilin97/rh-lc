module

public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedGroupGaloisAutomorphismMap
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapMul
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SameUnifRefl
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SameUnifRefl
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmMulEqOfResMulEq
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AdmissibleBasePowerSeries
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdentityPullbackDegeneration
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AdmissibleBasePowerSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapUnique

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedGroupGaloisAutomorphismMapStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_uniformisedGroup_galoisAutomorphism_map : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (σ : Gal ρ), ∃ a, GalMap hD U' σ a := by
  first | exact @GlobalTheory.Mum.exists_galMap | exact GlobalTheory.Mum.exists_galMap | (intros; apply GlobalTheory.Mum.exists_galMap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapMulStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.uniformisedGroup_galoisMap_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (σ τ : Gal ρ) (a b : G'.left ⟶ G'.left), GalMap hD U' σ a → GalMap hD U' τ b → GalMap hD U' (σ * τ) (a ≫ b) := by
  first | exact @GlobalTheory.Mum.galMap_mul | exact GlobalTheory.Mum.galMap_mul | (intros; apply GlobalTheory.Mum.galMap_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.PullPointIdentityDegeneration

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

theorem pmaps_self_of_tautological {X Y : Scheme.{0}} {L : LB X} {F : X ⟶ X} (hF : F = 𝟙 X)
    (w : LB.Iso L (L.pull F))
    (hw : ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (j k : L.ι), f z ∈ L.U j → f z ∈ L.U k →
      gw w f z j k = gm f z _ (L.g j k))
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    PMaps w φ φ ε t t (𝟙 Y) := by
  subst hF
  intro Z r z p q hp hq
  have hp' : ∀ k, φ k (r z) ∈ L.U (p k) := hp
  rw [Category.comp_id, gen_trans ht r z (j := p) (j' := q) (Set.mem_iInter.2 hp') (Set.mem_iInter.2 hq), trF]
  congr 1
  exact Finset.prod_congr rfl fun k _ => by rw [hw Z (r ≫ φ k) z (p k) (q k) (hp' k) (hq k)]

end GlobalTheory.TorsionFormCompare
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGalActRankOne

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

section
variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}}

end


open GlobalTheory.TorsionFormCompare in
theorem isPullUnif_refl {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G)
    (hD : IsPullDeg (RingHom.id R) D.toPre D.toPre) (hid : IsIdPull hD)
    (bc : G ≅ (Over.pullback (specOf (RingHom.id R))).obj G)
    (hbc : bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = 𝟙 _) : IsPullUnif (RingHom.id R) hD bc U U := by
  obtain ⟨hx, he, hw⟩ := hid
  have hs := specOf_id R
  have heG : eSec G ≫ bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = specOf (RingHom.id R) ≫ eSec G := by
    rw [hbc, hs, Category.comp_id]; exact (Category.id_comp _).symm
  refine (GlobalTheory.isPullUnif_iff_stalks R R I I _ D D hD A A G G bc U U).2
    ⟨isoPullId (Geo.Tor.idIso U.LG.L) hbc, (isGen_iff _).2 (isoPullId_pgen (idIso_isGen U.LG.isLB) hbc), heG,
      isoPullId_maps (idIso_maps U.LG) hbc hs heG, fun e => ⟨𝟙 _, by rw [hbc, Category.id_comp, Category.comp_id],
      ⟨by rw [he, Category.id_comp, Category.comp_id], fun x => ?_⟩, ?_⟩⟩
  · rw [hx x]
    exact ⟨fun κ => by rw [he, Category.id_comp, Category.comp_id],
      pmaps_self_of_tautological he hD.w hw _ _ _ ((U.gt e).t_gen x)⟩
  · intro Z r z jM jM' jL jL' h₁ h₂ h₃ h₄
    have h₁' : (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM := by rw [he] at h₁; exact h₁
    have h₃' : (fstG I e G).left (r z) ∈ U.LG.L.U jL := by rw [hbc] at h₃; exact h₃
    rw [Category.comp_id, gw_isoPullId _ hbc _ z jL jL' h₃' h₄, hw Z (r ≫ (U.gt e).pG.left) z jM jM' h₁' h₂]
    have H := (isGen_iff (U.w e)).1 (U.w_gen e) Z r z jM jM' (fun _ => jL) (fun _ => jL') h₁' h₂
      (mem_pull.2 h₃') (mem_pull.2 h₄)
    have hp : r z ∈ (U.LG.L.pull (fstG I e G).left).U (fun _ => jL) ⊓ (U.LG.L.pull (fstG I e G).left).U (fun _ => jL') :=
      ⟨mem_pull.2 h₃', mem_pull.2 h₄⟩
    have e₂ : gm r z _ ((U.LG.L.pull (fstG I e G).left).g (fun _ => jL) (fun _ => jL')) =
        gm (r ≫ (fstG I e G).left) z _ (U.LG.L.g jL jL') := by
      show gm r z _ (∏ _k : PUnit, (res _ (pullU _ _ (U.LG.L.g jL jL'))) ^ (1 : ℤ)) = _
      rw [Fintype.prod_unique, zpow_one]
      exact (gm_res r z _ hp _).trans (gm_pull r _ z (U.LG.L.U jL ⊓ U.LG.L.U jL') ⟨h₃', h₄⟩ _)
    rw [H, e₂]
    show _ = _ * gm (r ≫ (fstG I e G).left) z _ (U.LG.L.g jL jL')
    rw [mul_right_comm _ _⁻¹, inv_mul_cancel_right]

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapOne

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum


open GlobalTheory.TorsionFormCompare in
theorem galMap_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), GalMap hD U' 1 (𝟙 _) := by
  intro R _ _ _ _ R' _ _ _ ρ hρ D D' hD A' G' _ _ _ U'
  obtain ⟨W, hW, hψ⟩ := GlobalTheory.psiOnExists R' (maximalIdeal R') hρ.1 D'
  obtain ⟨h, hid⟩ := exists_isIdPull R' D'.toPre W hW hψ
  have gp : IsGrpPullback G' G' (specOf (RingHom.id R')) (𝟙 _) :=
    (@isGrpPullback_of_iso _ _ _ _ _ (Iso.refl G') (inferInstanceAs (IsMonHom (𝟙 G')))).congr (specOf_id R').symm rfl
  obtain ⟨bc, -, hbc⟩ := grpPullback_iso gp (isGrpPullback_pullback G' (specOf (RingHom.id R')))
  have hP : PullOver hD h := ⟨hid.1, fun b c _ hc => by rw [hc, hid.2.1, Category.id_comp]⟩
  exact ⟨gp, h, bc, hbc, isPullUnif_refl U' h hid bc hbc, hP⟩

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapOneStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.uniformisedGroup_galoisMap_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), GalMap hD U' 1 (𝟙 _) := by
  first | exact @GlobalTheory.Mum.galMap_one | exact GlobalTheory.Mum.galMap_one | (intros; apply GlobalTheory.Mum.galMap_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapUniqueStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.uniformisedGroup_galoisMap_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (σ : Gal ρ) (a a' : G'.left ⟶ G'.left), GalMap hD U' σ a → GalMap hD U' σ a' → a = a' := by
  first | exact @GlobalTheory.Mum.galMap_unique | exact GlobalTheory.Mum.galMap_unique | (intros; apply GlobalTheory.Mum.galMap_unique <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyGaloisActionPulledBackUniformisation

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem galAct_nonempty : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), Nonempty (GalAct ρ hD U') := by
  intro R _ _ _ hR R' _ _ _ ρ hfin hgal D D' hD A' G' _ _ hG U'
  have hex : ∀ σ : Gal ρ, ∃ a, GalMap hD U' σ a := GlobalTheory.T.exists_uniformisedGroup_galoisAutomorphism_map R hR R' ρ hfin D D' hD A' G' hG U'
  choose act hact using hex
  exact ⟨{ act := act
           cart := fun σ => (hact σ).1
           act_one := GlobalTheory.T.uniformisedGroup_galoisMap_unique R hR R' ρ hfin D D' hD A' G' hG U' 1 _ _ (hact 1) (GlobalTheory.T.uniformisedGroup_galoisMap_one R hR R' ρ hfin D D' hD A' G' hG U')
           act_mul := fun σ τ => GlobalTheory.T.uniformisedGroup_galoisMap_unique R hR R' ρ hfin D D' hD A' G' hG U' (σ * τ) _ _ (hact (σ * τ))
             (GlobalTheory.T.uniformisedGroup_galoisMap_mul R hR R' ρ hfin D D' hD A' G' hG U' σ τ _ _ (hact σ) (hact τ))
           unif := fun σ => (hact σ).2 }⟩

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyGaloisActionPulledBackUniformisationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.nonempty_galoisAction_pulledBack_uniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), Nonempty (GalAct ρ hD U') := by
  first | exact @GlobalTheory.Mum.galAct_nonempty | exact GlobalTheory.Mum.galAct_nonempty | (intros; apply GlobalTheory.Mum.galAct_nonempty <;> assumption)
end
end
