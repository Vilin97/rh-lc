module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegCompData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegOfValWOpen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
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
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegRescaleBothSidesStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegUniqueAndComp
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegCompOfFirstTop

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegCompTop

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

theorem exists_isPullDeg_comp_of_preimage {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''}
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D'')
    (hW : specOf i ⁻¹ᵁ p.W = ⊤) :
    ∃ r : IsPullDeg (j.comp i) D D'', proj r = proj q ≫ proj p ∧ ∀ x, r.xe x = p.xe (q.xe x) := by
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  obtain ⟨ψ', hv⟩ := PullDegCancelTop.exists_psiOn_pull p
  obtain ⟨g, hg'⟩ : ∃ g : (TK R'').left ⟶ (specOf i ⁻¹ᵁ p.W).toScheme,
      g ≫ (specOf i ⁻¹ᵁ p.W).ι = jK R'' ≫ specOf j :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro y -
      rw [Scheme.Opens.range_ι, hW]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  have hg : (g ≫ (specOf i ∣_ p.W)) ≫ p.W.ι = jK R'' ≫ specOf (j.comp i) := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hg', Category.assoc]
    exact congrArg (jK R'' ≫ ·) sc
  obtain ⟨r, hr₁, hr₂, -⟩ := PullDegCompData.exists_isPullDeg_of_valW D D'' p.psiW (g ≫ (specOf i ∣_ p.W)) hg gp w
    (T.pgen_comp D'.P.isLB g₁ g₂) hr (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have v₁ := hv (q.xe x) _ g z J J' hJ hJ'
      have v₂ := PsiEvenPull.psi_pull q x (𝟙 _) z hJ' hJ''
      have ag : val (ψ'.psi (q.xe x)) g z J' = val (q.psiW.psi (q.xe x)) (𝟙 _ ≫ q.g) z J' :=
        ArcSpecialise.psiOn_agree ψ' q.psiW _ _ _ (by rw [hg', Category.id_comp, q.g_comm]) hJ'
      have hx : D''.xK x ≫ proj q = g ≫ (specOf i ⁻¹ᵁ p.W).ι ≫ (D'.c (q.xe x)).left := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = _
        rw [Category.assoc, q.c_pr, ← Category.assoc g, hg', Category.assoc]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      change _ = (om q.w z J' J'' (𝟙 _ ≫ D''.xK x))⁻¹ * _ at v₂
      rw [ag, v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r, hr₁, hr₂⟩

theorem exists_isPullDeg_comp_top : ∀ {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D''), p.W = ⊤ → ∃ r : IsPullDeg (j.comp i) D D'', r.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (j.comp i)) = (q.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf j)) ≫ p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, r.xe x = p.xe (q.xe x) := by
  intro R R' R'' _ _ _ _ _ _ i j D D' D'' p q e
  exact exists_isPullDeg_comp_of_preimage p q (by rw [e]; rfl)

end GlobalTheory.PullDegCompTop
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegCompOfFirstTopStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_isPullDeg_comp_of_first_top : ∀ {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D''), p.W = ⊤ → ∃ r : IsPullDeg (j.comp i) D D'', r.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (j.comp i)) = (q.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf j)) ≫ p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, r.xe x = p.xe (q.xe x) := by
  first | exact @GlobalTheory.PullDegCompTop.exists_isPullDeg_comp_top | exact GlobalTheory.PullDegCompTop.exists_isPullDeg_comp_top | (intros; apply GlobalTheory.PullDegCompTop.exists_isPullDeg_comp_top <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegWholeSpectrum

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullDegWhole

theorem exists_isPullDeg_top : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {i : R →+* R'} {D : DegPre R} {D' : DegPre R'} (p : IsPullDeg i D D'), Nonempty (PsiOn D ⊤) → ∃ p' : IsPullDeg i D D', p'.W = ⊤ ∧ p'.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, p'.xe x = p.xe x := by
  intro R R' _ _ _ _ i D D' p ⟨ψ⟩
  obtain ⟨g, hg⟩ : ∃ g : (TK R').left ⟶ (⊤ : (Spec (CommRingCat.of R)).Opens).toScheme,
      g ≫ (⊤ : (Spec (CommRingCat.of R)).Opens).ι = jK R' ≫ specOf i :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  refine ⟨{ p with W := ⊤, psiW := ψ, g := g, g_comm := hg, psi_pr := fun x => ?_ }, rfl, rfl, fun _ => rfl⟩
  obtain ⟨b, hb, hc⟩ := p.psi_pr x
  refine ⟨b, hb, corr_of_val D.P.isLB fun y J hJ => (val_corr hJ hc _).trans (by
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    exact GlobalTheory.ArcSpecialise.psiOn_agree p.psiW ψ _ _ _
      (by rw [Category.assoc, Category.assoc]; exact congrArg _ (p.g_comm.trans hg.symm)) hJ)⟩

end GlobalTheory.PullDegWhole
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegWholeSpectrumStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_isPullDeg_whole_spectrum : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {i : R →+* R'} {D : DegPre R} {D' : DegPre R'} (p : IsPullDeg i D D'), Nonempty (PsiOn D ⊤) → ∃ p' : IsPullDeg i D D', p'.W = ⊤ ∧ p'.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, p'.xe x = p.xe x := by
  first | exact @GlobalTheory.PullDegWhole.exists_isPullDeg_top | exact GlobalTheory.PullDegWhole.exists_isPullDeg_top | (intros; apply GlobalTheory.PullDegWhole.exists_isPullDeg_top <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverPullbackMapLeftCompPullbackFstScheme

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section

namespace GlobalTheory.Mum

theorem over_pullback_map_left_comp_pullbackFst_scheme {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (g : X ⟶ Y) :
    ((Over.pullback f).map g).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ g.left := by
  simp only [Over.pullback_map_left, pullback.lift_fst]

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseStableUnderPullbackOfData

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.DivFromPull

theorem divFrom_pull : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (Q : DegPre R) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (Q' : DegPre V) [Module (𝓞 E) Q'.X] (oQ' : letI := H.starRing; Q'.OAct (𝓞 E)) (iw : L.W →+* R) (θ : R →+* V) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X) (hD : IsPullDeg θ Q Q') (e' : Q'.X ≃ₗ[𝓞 E] L.D.X), (∀ y, e' y = e (hD.xe y)) → (letI := H.starRing; ∀ x, oQ'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ)).map (oQ.onB.act x)) → (∀ k, θ (s k) ≠ 0) → DivFrom L Q oQ iw s ε e → DivFrom L Q' oQ' (θ.comp iw) (fun k => θ (s k)) ε e' := by
  intro E _ _ _ H D' l c L R V _ _ _ _ Q _ oQ Q' _ oQ' iw θ I _ s ε e hD e' he' hact hs hdiv
  obtain ⟨g, hD0, hg, hxe, hac⟩ := hdiv
  have ψL : Nonempty (PsiOn (mulDeg L.D l.M') ⊤) := GlobalTheory.ArcPull.nonempty_psiOn_top _ (fun y => L.gen (l.M' • y))
  obtain ⟨hD1, hW1, hp1, hx1⟩ := GlobalTheory.T.exists_isPullDeg_whole_spectrum hD0 ψL
  have ψR : Nonempty (PsiOn (GlobalTheory.PolDeg.rescale Q g) ⊤) := by
    have := GlobalTheory.PullDegUniq.nonempty_psiOn_pull hD1
    rw [hW1] at this
    simpa using this

  let n : Q'.X → I → ℤ := fun y k => (l.M' : ℤ) * ε k (e' y) (H.w0 • e' y)
  have hs0 : ∀ k, algebraMap V (FractionRing V) (θ (s k)) ≠ 0 := fun k =>
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 (hs k)
  have hr0 : ∀ k, algebraMap R (FractionRing R) (s k) ≠ 0 := fun k =>
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (fun h => hs k (by rw [h, map_zero]))
  let g' : Q'.X → (FractionRing V)ˣ := fun y =>
    (Units.mk0 (∏ k, algebraMap V (FractionRing V) (θ (s k)) ^ n y k)
      (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hs0 k)))⁻¹
  have hab : ∀ y, ∃ a b : R, θ b ≠ 0 ∧ (g (hD.xe y) : FractionRing R) * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a ∧
      (g' y : FractionRing V) * algebraMap V (FractionRing V) (θ b) = algebraMap V (FractionRing V) (θ a) := by
    intro y
    have key : ∀ {K : Type} [Field K] (x : K), x ≠ 0 → ∀ m : ℤ, x ^ (-m) * x ^ m.toNat = x ^ (-m).toNat := by
      intro K _ x hx m
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hx]
      congr 1
      omega
    have hgz : (g (hD.xe y) : FractionRing R) = ∏ k, algebraMap R (FractionRing R) (s k) ^ (-n y k) := by
      have h := hg (hD.xe y)
      rw [Units.val_inv_eq_inv_val] at h
      rw [← inv_inv (g (hD.xe y) : FractionRing R), h, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [zpow_neg]
      simp only [n, he' y]
    have hg'y : (g' y : FractionRing V) = ∏ k, algebraMap V (FractionRing V) (θ (s k)) ^ (-n y k) := by
      simp only [g', Units.val_inv_eq_inv_val, Units.val_mk0, ← Finset.prod_inv_distrib, zpow_neg]
    refine ⟨∏ k, s k ^ (-n y k).toNat, ∏ k, s k ^ (n y k).toNat, ?_, ?_, ?_⟩
    · rw [map_prod]
      exact Finset.prod_ne_zero_iff.2 fun k _ => by rw [map_pow]; exact pow_ne_zero _ (hs k)
    · rw [hgz, map_prod, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [map_pow, map_pow]
      exact key _ (hr0 k) _
    · rw [hg'y, map_prod, map_prod, map_prod, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [map_pow, map_pow, map_pow, map_pow]
      exact key _ (hs0 k) _
  obtain ⟨h1, hp2, hx2⟩ := GlobalTheory.T.exists_isPullDeg_rescale_both_sides hD g g' ψR hab
  obtain ⟨r, hpr, hxr⟩ := GlobalTheory.T.exists_isPullDeg_comp_of_first_top hD1 h1 hW1
  refine ⟨g', r, fun y => ?_, fun y => ?_, fun x => ?_⟩
  · simp only [g', Units.val_inv_eq_inv_val, inv_inv, Units.val_mk0, map_zpow]
    rfl
  · exact (hxr y).trans ((hx1 _).trans ((congrArg hD0.xe (hx2 y)).trans ((hxe _).trans (he' y).symm)))
  · letI := H.starRing
    have c₁ : (oQ'.onB.act x).left ≫ hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) =
        hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) ≫ (oQ.onB.act x).left := by
      have := congrArg (fun m => m.left ≫ pullback.fst Q.P.A.hom (specOf θ)) (hact x)
      simpa only [Over.comp_left, Category.assoc, GlobalTheory.Mum.over_pullback_map_left_comp_pullbackFst_scheme] using this
    have hpr' : r.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf (θ.comp iw)) =
        (hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ)) ≫ hD0.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) :=
      hpr.trans (by rw [hp1]; exact congrArg (· ≫ _) hp2)
    have key : (oQ'.onB.act x).left ≫ ((hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ)) ≫ hD0.e.hom.left ≫
        pullback.fst L.D.P.A.hom (specOf iw)) = ((hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ)) ≫
        hD0.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) ≫ (L.oa.onB.act x).left := by
      simp only [Category.assoc] at c₁ hac ⊢
      rw [reassoc_of% c₁]
      exact congrArg _ (congrArg _ ((hac x).trans (Category.assoc _ _ _).symm))
    exact (congrArg _ hpr').trans (key.trans (congrArg (· ≫ _) hpr'.symm))

end GlobalTheory.UCanon.DivFromPull
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseStableUnderPullbackOfDataStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.comesFromBase_stable_under_pullback_of_data : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (Q : DegPre R) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (Q' : DegPre V) [Module (𝓞 E) Q'.X] (oQ' : letI := H.starRing; Q'.OAct (𝓞 E)) (iw : L.W →+* R) (θ : R →+* V) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X) (hD : IsPullDeg θ Q Q') (e' : Q'.X ≃ₗ[𝓞 E] L.D.X), (∀ y, e' y = e (hD.xe y)) → (letI := H.starRing; ∀ x, oQ'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ)).map (oQ.onB.act x)) → (∀ k, θ (s k) ≠ 0) → DivFrom L Q oQ iw s ε e → DivFrom L Q' oQ' (θ.comp iw) (fun k => θ (s k)) ε e' := by
  first | exact @GlobalTheory.UCanon.DivFromPull.divFrom_pull | exact GlobalTheory.UCanon.DivFromPull.divFrom_pull | (intros; apply GlobalTheory.UCanon.DivFromPull.divFrom_pull <;> assumption)
end
end
