module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodLevelMultipleSameAdelicPart
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulipointLiftToFinerLevelCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Mathlib.Algebra.Order.Star.Int
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.UnifAt

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodLevelMultipleSameAdelicPartStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

theorem _root_.GlobalTheory.T.exists_goodLevel_multiple_same_adelicPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H), ∃ l₂ : Level H, l.Dvd l₂ ∧ l₂.A = l.A ∧ ∀ q : ℕ, q.Prime → l₂.GoodAt q := by
  first | exact @GlobalTheory.GoodMultipleLevel.exists_good_multiple | exact GlobalTheory.GoodMultipleLevel.exists_good_multiple | (intros; apply GlobalTheory.GoodMultipleLevel.exists_good_multiple <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFramedDataCompleteDVRExtension

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

noncomputable section

namespace GlobalTheory.FramedExt

theorem eSec_hom {S : Scheme.{0}} (X : Over S) [GrpObj X] : eSec X ≫ X.hom = 𝟙 _ := by
  simp [eSec]

theorem dualMapR_comp_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    (Chart.dualMapR f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := by
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_ext {R R' : Type} [CommRing R] [CommRing R'] (F₁ F₂ : DualNumber R →+* DualNumber R')
    (h : ∀ a : R, F₁ (algebraMap R (DualNumber R) a) = F₂ (algebraMap R (DualNumber R) a))
    (hε : F₁ DualNumber.eps = F₂ DualNumber.eps) : F₁ = F₂ := by
  refine RingHom.ext fun x => ?_
  have hx : x = algebraMap R (DualNumber R) x.fst + algebraMap R (DualNumber R) x.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [hx, map_add (f := _), map_add (f := _), map_mul, map_mul, h, h, hε]

theorem generates_of_flat {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {R R₂ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R₂] [IsDomain R₂] (φ : R →+* R₂) (hφ : Function.Injective φ) (G : SAB H (Sp R)) (G₂ : SAB H (Sp R₂)) (m : SABMap G₂ G (spMap φ)) (wI : G₂.PP.L.Iso (G.PP.L.pull m.φ)) (hwI : LB.Gen.IsGen wI) (θ : G.PP.L.Sec) (θ₂ : G₂.PP.L.Sec) (hθ : IsoMaps wI θ₂ (thfPull G.PP.L m.φ θ)) : Generates (X := G.G) θ → Generates (X := G₂.G) θ₂ := by
  intro hgen
  letI := φ.toAlgebra
  have : FaithfulSMul R R₂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have : Module.Flat R R₂ := inferInstance
  haveI : IsSeparated G.G.hom := G.semi.separated
  haveI : QuasiCompact G.G.hom := G.semi.quasiCompact
  haveI : CompactSpace G.G.left := QuasiCompact.compactSpace_of_compactSpace G.G.hom
  have hinter : ∀ U W : G.G.left.Opens, IsAffineOpen U → IsAffineOpen W → IsAffineOpen (U ⊓ W) :=
    fun U W hU hW => isAffineHom_diagonal_iff.mp (inferInstance : IsAffineHom (pullback.diagonal G.G.hom)) ⊤
      (isAffineOpen_top _) U le_top W le_top hU hW
  have Hpb : IsPullback m.φ G₂.G.hom G.G.hom (Spec.map (CommRingCat.ofHom (algebraMap R R₂))) := m.cart.1
  exact fun s' => ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.flatBC_iso G.G.hom G₂.G.hom m.φ Hpb hinter G.PP.L G.PP.isLB θ hgen
    G₂.PP.L G₂.PP.isLB wI hwI θ₂ _ hθ (fun _ _ => rfl) s'

theorem isFibreOf_trans {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (hL : L.IsLB) (rig : (L.pull (eSec G)).Gen) (θ : L.Sec) {n : ℕ} (w : Fin n → (epsR R ⟶ G)) (k : KeyIn R') (k' : KeyIn R'') (f : R →+* R') (g : R' →+* R'') : IsFibreOf k G L rig θ w f → KeyPB k' k g → IsFibreOf k' G L rig θ w (g.comp f) := by
  intro H H'
  obtain ⟨φ, he, w₀, hg, F, hp, hw, hr, hs, hF, hε, hv⟩ := H
  obtain ⟨φ', he', w', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := H'
  have g₀ := (isGen_iff w₀).1 hw
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp k.P.isLB w₀ w' g₀ g' hL k'.P.isLB
  have he'' : eSec k'.P.A ≫ φ' ≫ φ = spMap (g.comp f) ≫ eSec G := by
    rw [← Category.assoc, he', Category.assoc, he, spMap_comp, Category.assoc]
  refine ⟨φ' ≫ φ, he'', w'', hg'.trans hg, F'.comp F, (hp'.comp hp).congr (spMap_comp f g).symm rfl,
    (isGen_iff w'').2 (T.pgen_comp k.P.isLB g₀ g'), ?_, ?_, fun a => ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff w₀ _ (fun _ => eSec G) _ k.rig rig (spMap f) _
      (rigPull_le φ (spMap f) he L) (fun _ => rfl)).1 hr
    have r₁ := (maps_iff w' _ (fun _ => eSec k.P.A) _ k'.rig k.rig (spMap g) _
      (rigPull_le φ' (spMap g) he' k.P.L) (fun _ => rfl)).1 hr'
    have r₂ := T.pmaps_comp k.P.isLB (fun _ => he') r₀ r₁
    rw [← spMap_comp] at r₂
    exact (maps_iff w'' _ (fun _ => eSec G) _ k'.rig rig (spMap (g.comp f)) _
      (rigPull_le (φ' ≫ φ) (spMap (g.comp f)) he'' L) (fun _ => rfl)).2 r₂
  · refine GlobalTheory.KeyPow.appLE_eq_of_stalk w'' θ k'.th fun z j k₀ hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart k.P.isLB (φ' z)
    have a := GlobalTheory.KeyComp.stalk_of_appLE_eq w₀ θ k.th hs (𝟙 _ ≫ φ') z j i hj hi
    have b := GlobalTheory.KeyComp.stalk_of_appLE_eq w' k.th k'.th hs' (𝟙 _) z i k₀ hi hk
    rw [T _ (𝟙 _) z j i k₀ hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]
  · rw [RingHom.comp_apply, hF, hF', RingHom.comp_apply]
  · rw [RingHom.comp_apply, hε, hε']
  · rw [← Category.assoc, hv', Category.assoc, hv, spMap_comp, Category.assoc]
    rfl

theorem isFibreOf_descend {R R₂ K : Type} [CommRing R] [CommRing R₂] [CommRing K] (φ : R →+* R₂) (f : R₂ →+* K) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (L : LB G.left) (hL : L.IsLB) (rig : (L.pull (eSec G)).Gen) (L₂ : LB G₂.left) (hL₂ : L₂.IsLB) (rig₂ : (L₂.pull (eSec G₂)).Gen) (ψ : G₂.left ⟶ G.left) (hψ : IsGrpPullback G₂ G (spMap φ) ψ) (he : eSec G₂ ≫ ψ = spMap φ ≫ eSec G) (wI : L₂.Iso (L.pull ψ)) (hwI : LB.Gen.IsGen wI) (hrig : LB.Gen.Maps (LB.linCombIso wI (fun _ => eSec G₂) fun _ => 1) rig₂ (rigPullOf ψ (spMap φ) he L rig)) (θ : L.Sec) (θ₂ : L₂.Sec) (hθ : IsoMaps wI θ₂ (thfPull L ψ θ)) {n : ℕ} (w : Fin n → (epsR R ⟶ G)) (w₂ : Fin n → (epsR R₂ ⟶ G₂)) (hw : ∀ i, (w₂ i).left ≫ ψ = spMap (Chart.dualMapR φ) ≫ (w i).left) (k : KeyIn K) : IsFibreOf k G L rig θ w (f.comp φ) → IsFibreOf k G₂ L₂ rig₂ θ₂ w₂ f := by
  intro H
  obtain ⟨φk, hek, e, hg, F, hp, hgen, hr, hs, hF, hε, hv⟩ := H
  obtain ⟨ψ₂, hfac, hbase⟩ : ∃ ψ₂ : k.P.A.left ⟶ G₂.left, ψ₂ ≫ ψ = φk ∧ ψ₂ ≫ G₂.hom = k.P.A.hom ≫ spMap f :=
    ⟨hψ.1.lift φk (k.P.A.hom ≫ spMap f) (by rw [hp.1.w, spMap_comp, Category.assoc]),
      hψ.1.lift_fst _ _ _, hψ.1.lift_snd _ _ _⟩
  subst hfac
  have hp₂ : IsGrpPullback k.P.A G₂ (spMap f) ψ₂ := hψ.cancel (hp.congr (spMap_comp φ f) rfl) hbase
  have he₂ : eSec k.P.A ≫ ψ₂ = spMap f ≫ eSec G₂ := by
    apply hψ.1.hom_ext
    · rw [Category.assoc, hek, Category.assoc, he, spMap_comp, Category.assoc]
    · rw [Category.assoc, hbase, ← Category.assoc, eSec_hom, Category.assoc, eSec_hom]
      simp
  have gI := (isGen_iff wI).1 hwI
  have g₀ := (isGen_iff e).1 hgen
  obtain ⟨e₂, T⟩ := exists_cancel hL wI e gI g₀ hL₂ k.P.isLB
  have hFe : F = (Chart.dualMapR f).comp (Chart.dualMapR φ) := dual_ext _ _ (fun a => by
      simp only [hF, RingHom.comp_apply]
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by rw [hε]; ext <;> simp [Chart.dualMapR])
  refine ⟨ψ₂, he₂, e₂, hg, Chart.dualMapR f, hp₂, (isGen_iff e₂).2 (T.pgen_cancel hL gI g₀), ?_, ?_,
    fun a => ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff wI _ (fun _ => eSec G) _ rig₂ rig (spMap φ) _
      (rigPull_le ψ (spMap φ) he L) (fun _ => rfl)).1 hrig
    have r'' := (maps_iff e _ (fun _ => eSec G) _ k.rig rig (spMap (f.comp φ)) _
      (rigPull_le (ψ₂ ≫ ψ) (spMap (f.comp φ)) hek L) (fun _ => rfl)).1 hr
    rw [spMap_comp] at r''
    have r₂ := T.pmaps_cancel hL (fun _ => he₂) r₀ r''
    exact (maps_iff e₂ _ (fun _ => eSec G₂) _ k.rig rig₂ (spMap f) _
      (rigPull_le ψ₂ (spMap f) he₂ L₂) (fun _ => rfl)).2 r₂
  · have hθ' : ∀ (j : (L.pull ψ).ι) (i : L₂.ι) (hle : (L.pull ψ).U j ⊓ L₂.U i ≤ ψ ⁻¹ᵁ L.U (j PUnit.unit)),
        (Scheme.Hom.appLE ψ (L.U (j PUnit.unit)) ((L.pull ψ).U j ⊓ L₂.U i) hle).hom (θ.f (j PUnit.unit)) =
          (show Γ(G₂.left, (L.pull ψ).U j ⊓ L₂.U i) from (wI.s (j, i)).val) * resG _ inf_le_right (θ₂.f i) := by
      intro j i hle
      refine Eq.trans ?_ (hθ j i)
      dsimp only [thfPull]
      first
        | (erw [Scheme.Hom.appLE_map])
        | (simp only [Scheme.Hom.appLE_map])
        | (rw [← Scheme.Hom.appLE_map ψ _ (homOfLE inf_le_left).op]; rfl)
    refine GlobalTheory.KeyPow.appLE_eq_of_stalk e₂ θ₂ k.th fun z j k₀ hj hk => ?_
    obtain ⟨jL, hjL⟩ := exists_chart hL (ψ (ψ₂ z))
    have a := GlobalTheory.KeyComp.stalk_of_appLE_eq e θ k.th hs (𝟙 _) z jL k₀ hjL hk
    have b := GlobalTheory.KeyComp.stalk_of_appLE_eq wI θ θ₂ hθ' (𝟙 _ ≫ ψ₂) z jL j hjL hj
    rw [Category.assoc] at b
    rw [T _ (𝟙 _) z jL j k₀ hjL hj hk, b, Units.val_mul, _root_.mul_assoc] at a
    exact (Units.mul_right_inj _).1 a
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hψ.1.hom_ext
    · rw [Category.assoc, hv i, Category.assoc, hw, ← Category.assoc, hFe, spMap_comp]
    · rw [Category.assoc, hbase, ← Category.assoc, Over.w (k.v i), Category.assoc, Over.w (w₂ (Fin.cast hg i))]
      simp only [epsR, Over.mk_hom]
      rw [← spMap_comp, ← spMap_comp, dualMapR_comp_algebraMap]

theorem exists_framed_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (T T' : CDVR) (iT : T.Fr →+* T'.Fr) (φ : T.V →+* T'.V), (∀ a : T.V, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)), SABMap t' G (spMap (algebraMap T.V T.Fr)) → ∀ (n : ℕ) (w : Fin n → (epsR T.V ⟶ G.G)), IsLieBasis w → ∀ (θ : G.PP.L.Sec), Generates (X := G.G) θ → ∀ (k : KeyIn T.Fr), IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr) → ∃ (G' : SAB H (Sp T'.V)) (t'' : SAB H (Sp T'.Fr)) (_ : SABMap t'' t' (spMap iT)) (_ : SABMap t'' G' (spMap (algebraMap T'.V T'.Fr))) (n' : ℕ) (w' : Fin n' → (epsR T'.V ⟶ G'.G)) (θ' : G'.PP.L.Sec) (k' : KeyIn T'.Fr), IsLieBasis w' ∧ Generates (X := G'.G) θ' ∧ IsFibreOf k' G'.G G'.PP.L G'.PP.rig θ' w' (algebraMap T'.V T'.Fr) ∧ KeyPB k' k iT := by
  intro E _ _ _ H T T' iT φ hφ G t' m2 n w hw θ hθ k hk
  have hφ' : (algebraMap T'.V T'.Fr).comp φ = iT.comp (algebraMap T.V T.Fr) := RingHom.ext hφ
  have hsq : spMap iT ≫ spMap (algebraMap T.V T.Fr) = spMap (algebraMap T'.V T'.Fr) ≫ spMap φ := by
    rw [← spMap_comp, ← spMap_comp, hφ']
  have tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g → SABMap s' s f →
      Nonempty (SABMap s' s g) := by
    intro S S' s s' f g h m
    subst h
    exact ⟨m⟩
  obtain ⟨G₂, ⟨m⟩⟩ : ∃ G₂ : SAB H (Sp T'.V), Nonempty (SABMap G₂ G (spMap φ)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap φ) G
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t₂, ⟨p⟩⟩ : ∃ t₂ : SAB H (Sp T'.Fr), Nonempty (SABMap t₂ t' (spMap iT)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap iT) t'
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨a₂, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m2 p
  obtain ⟨b₂⟩ := tr hsq a₂
  obtain ⟨m2', -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m b₂
  obtain ⟨w', hw', hww⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ φ G.G G₂.G m.φ m.cart G.semi.smooth n w hw
  obtain ⟨k', hk'⟩ := GlobalTheory.KeyPow.exists_keyPB_ring k iT
  obtain ⟨wI, hwI, hrI, -⟩ := m.lin
  obtain ⟨θ₂, hθ₂⟩ := GlobalTheory.ArcQ.NormalForm.exists_isoMaps wI hwI G.PP.isLB G₂.PP.isLB (thfPull G.PP.L m.φ θ)
  have he : eSec G₂.G ≫ m.φ = spMap φ ≫ eSec G.G := m.cm.e_comm.trans (congrArg (· ≫ eSec G.G) m.base)
  have hr : ∀ (e : Sp T'.V ⟶ Sp T.V) (_ : m.cm.e = e) (he : eSec G₂.G ≫ m.φ = e ≫ eSec G.G),
      rigPullOf m.φ e he G.PP.L G.PP.rig = m.cm.rigPull G.PP.L G.PP.rig := by
    rintro _ rfl _
    rfl
  have hrig : LB.Gen.Maps (LB.linCombIso wI (fun _ => eSec G₂.G) fun _ => 1) G₂.PP.rig
      (rigPullOf m.φ (spMap φ) he G.PP.L G.PP.rig) := by
    rw [hr _ m.base he]; exact hrI
  have h1 := isFibreOf_trans G.G G.PP.L G.PP.isLB G.PP.rig θ w k k' (algebraMap T.V T.Fr) iT hk hk'
  rw [← hφ'] at h1
  have hinj : Function.Injective φ := fun a b hab => IsFractionRing.injective T.V T.Fr
    (iT.injective (by rw [← hφ a, ← hφ b, hab]))
  exact ⟨G₂, t₂, p, m2', n, w', θ₂, k', hw', generates_of_flat φ hinj G G₂ m wI hwI θ θ₂ hθ₂ hθ,
    isFibreOf_descend φ (algebraMap T'.V T'.Fr) G.G G₂.G G.PP.L G.PP.isLB G.PP.rig G₂.PP.L G₂.PP.isLB G₂.PP.rig m.φ
      m.cart he wI hwI hrig θ θ₂ hθ₂ w w' hww k' h1, hk'⟩

end GlobalTheory.FramedExt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFramedDataCompleteDVRExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

theorem _root_.GlobalTheory.T.exists_integralFramedData_completeDVR_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (T T' : CDVR) (iT : T.Fr →+* T'.Fr) (φ : T.V →+* T'.V), (∀ a : T.V, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)), SABMap t' G (spMap (algebraMap T.V T.Fr)) → ∀ (n : ℕ) (w : Fin n → (epsR T.V ⟶ G.G)), IsLieBasis w → ∀ (θ : G.PP.L.Sec), Generates (X := G.G) θ → ∀ (k : KeyIn T.Fr), IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr) → ∃ (G' : SAB H (Sp T'.V)) (t'' : SAB H (Sp T'.Fr)) (_ : SABMap t'' t' (spMap iT)) (_ : SABMap t'' G' (spMap (algebraMap T'.V T'.Fr))) (n' : ℕ) (w' : Fin n' → (epsR T'.V ⟶ G'.G)) (θ' : G'.PP.L.Sec) (k' : KeyIn T'.Fr), IsLieBasis w' ∧ Generates (X := G'.G) θ' ∧ IsFibreOf k' G'.G G'.PP.L G'.PP.rig θ' w' (algebraMap T'.V T'.Fr) ∧ KeyPB k' k iT := by
  first | exact @GlobalTheory.FramedExt.exists_framed_ext | exact GlobalTheory.FramedExt.exists_framed_ext | (intros; apply GlobalTheory.FramedExt.exists_framed_ext <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulipointLiftToFinerLevelCompleteDVRStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

theorem _root_.GlobalTheory.T.modulipoint_lift_to_finerLevel_completeDVR : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l₂ : Level H) (Xo : Moduli Dw l) (Xo₂ : Moduli Dw l₂) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.Dvd l₂ → l₂.A = l.A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (x : Sp T.Fr ⟶ Xo.X), x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom) → ∃ (c₂ : Coeff l₂) (la₂ : HeightOneSpectrum (𝓞 c₂.F)) (T' : CDVR) (iT : T.Fr →+* T'.Fr) (φ : T.V →+* T'.V) (e' : ℕ) (io₂ : c₂.F →+* T'.Fr) (e₂ : ℕ) (x₂ : Sp T'.Fr ⟶ Xo₂.X) (r : Xo₂.X ⟶ Xo.X) (_ : SABMap Xo₂.univ.t Xo.univ.t r), 0 < e' ∧ (∀ a : T.Fr, vV T'.V (iT a) = (e' : ℤ) * vV T.V a) ∧ (∀ a : T.V, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) ∧ OverLa la₂ T'.V io₂ e₂ ∧ x₂ ≫ Xo₂.s = spMap (io₂.comp (IntermediateField.inclusion c₂.le).toRingHom) ∧ x₂ ≫ r = spMap iT ≫ x := by
  first | exact @GlobalTheory.LevelLift.lift_to_finer_level | exact GlobalTheory.LevelLift.lift_to_finer_level | (intros; apply GlobalTheory.LevelLift.lift_to_finer_level <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleIsUnitAtBadLevelPlace

section

@[expose] public section

noncomputable section

namespace GlobalTheory.KeyBadPrime

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

theorem key_unit_bad : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (κ : KeyRule), IsKeyRule κ → 1 ≤ Dw.p + Dw.q → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → ¬ l.GoodAt p → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (x : Sp T.Fr ⟶ Xo.X), x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom) → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)), SABMap t' Xo.univ.t x → SABMap t' G (spMap (algebraMap T.V T.Fr)) → ∀ (n : ℕ) (w : Fin n → (epsR T.V ⟶ G.G)), IsLieBasis w → ∀ (θ : G.PP.L.Sec), Generates (X := G.G) θ → ∀ (k : KeyIn T.Fr), IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr) → ∃ u : T.Vˣ, (κ T.Fr k : T.Fr) = algebraMap T.V T.Fr u := by
  intro E _ _ _ H Dw l Xo c κ hκ hpq la p hp hpl hbad T io e ho x hxs G t' m1 m2 n w hw θ hθ k hk
  obtain ⟨l₂, hd, hA, hg₂⟩ := GlobalTheory.T.exists_goodLevel_multiple_same_adelicPart E H l
  obtain ⟨Xo₂⟩ := GlobalTheory.Moduli.moduli_scheme_exists E H Dw l₂ hpq
  obtain ⟨c₂, la₂, T', iT, φ, e', io₂, e₂, x₂, r, m, he', hv, hφ, ho₂, hxs₂, hx₂⟩ :=
    GlobalTheory.T.modulipoint_lift_to_finerLevel_completeDVR E H Dw l l₂ Xo Xo₂ c hpq hd hA la T io e ho x hxs
  obtain ⟨G', t'', mt, m2', n', w', θ', k', hw', hθ', hk', hpb⟩ := GlobalTheory.T.exists_integralFramedData_completeDVR_extension E H T T' iT φ hφ G t' m2 n w hw θ hθ k hk
  obtain ⟨a₁, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m1 mt
  obtain ⟨m1', -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m (PullbackSections.sabMapCast a₁ hx₂.symm)
  obtain ⟨u', hu'⟩ := GlobalTheory.KeyIntegralVal.key_unit hκ hpq hg₂ ho₂ hxs₂ m1' m2' hw' hθ' k' hk'
  have h1 : (κ T'.Fr k' : T'.Fr) = iT (κ T.Fr k : T.Fr) := hκ.2.1 T.Fr T'.Fr iT k k' hpb
  set a : T.Fr := (κ T.Fr k : T.Fr) with ha
  have ha0 : a ≠ 0 := Units.ne_zero _
  have hu0 : ∀ (V : CDVR) (u : V.Vˣ), vV V.V (algebraMap V.V V.Fr u) = 0 := by
    intro V u
    have hne : ∀ u : V.Vˣ, algebraMap V.V V.Fr u ≠ 0 := fun u => (u.isUnit.map _).ne_zero
    have nn : ∀ b : V.V, 0 ≤ vV V.V (algebraMap V.V V.Fr b) := fun b => by
      by_cases h : algebraMap V.V V.Fr b = 0
      · simp [h, vV]
      have := (WithZero.log_le_log (valV_ne_zero (V := V.V) h) one_ne_zero).2
        (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ b)
      rw [WithZero.log_one] at this
      rw [vV]; omega
    have h := vV_mul (V := V.V) (hne u) (hne u⁻¹)
    rw [← map_mul, Units.mul_inv, map_one, show vV V.V (1 : V.Fr) = 0 by simp [vV]] at h
    have := nn u
    have := nn (u⁻¹ : V.Vˣ)
    omega
  have hva : vV T.V a = 0 := by
    have h2 := hv a
    rw [← h1, hu', hu0] at h2
    have : (0 : ℤ) < e' := by exact_mod_cast he'
    nlinarith
  have hvi : vV T.V a⁻¹ = 0 := by
    have h := vV_mul (V := T.V) ha0 (inv_ne_zero ha0)
    rw [mul_inv_cancel₀ ha0, show vV T.V (1 : T.Fr) = 0 by simp [vV], hva] at h
    omega
  obtain ⟨b, hb⟩ := Formalism.L2.PjFree.mem_range_of_vV_nonneg (V := T.V) hva.ge
  obtain ⟨b', hb'⟩ := Formalism.L2.PjFree.mem_range_of_vV_nonneg (V := T.V) hvi.ge
  have hbb : b * b' = 1 := IsFractionRing.injective T.V T.Fr (by rw [map_mul, hb, hb', mul_inv_cancel₀ ha0, map_one])
  exact ⟨⟨b, b', hbb, by rw [mul_comm]; exact hbb⟩, hb.symm⟩

end GlobalTheory.KeyBadPrime
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleIsUnitAtBadLevelPlaceStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

theorem _root_.GlobalTheory.T.thetaKeyRule_isUnit_at_bad_level_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (κ : KeyRule), IsKeyRule κ → 1 ≤ Dw.p + Dw.q → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → ¬ l.GoodAt p → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (x : Sp T.Fr ⟶ Xo.X), x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom) → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)), SABMap t' Xo.univ.t x → SABMap t' G (spMap (algebraMap T.V T.Fr)) → ∀ (n : ℕ) (w : Fin n → (epsR T.V ⟶ G.G)), IsLieBasis w → ∀ (θ : G.PP.L.Sec), Generates (X := G.G) θ → ∀ (k : KeyIn T.Fr), IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr) → ∃ u : T.Vˣ, (κ T.Fr k : T.Fr) = algebraMap T.V T.Fr u := by
  first | exact @GlobalTheory.KeyBadPrime.key_unit_bad | exact GlobalTheory.KeyBadPrime.key_unit_bad | (intros; apply GlobalTheory.KeyBadPrime.key_unit_bad <;> assumption)
end
end
