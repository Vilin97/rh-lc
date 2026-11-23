module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllMapCancelAndSabMapCancel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackTorsionPoints
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualFamilyIsBasisStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelEigenvectorsActionStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinearStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOfSmoothStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFunctorialMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalenceStatement
public import Development.WeilBound.CoreStatements.SesquilinearFractions.GLieInt
import Development.WeilBound.CoreStatements.SesquilinearFractions.GLieIntA
import Development.WeilBound.CoreStatements.SesquilinearFractions.GLieIntC
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsogenyProductDecompositionStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsogenyDecompositionProduct

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

open PositivityTheory.Xgf.isogeny_decomposition_product in

theorem _root_.GlobalTheory.CompanionTheory.Relay.isogeny_decomposition_product : ∀ (R V : Type) [CommRing R] [CommRing V] [IsLocalRing V] (f : R →+* V) (n N : ℕ) (C : Fin n → Out.PolAV (Sp R)) (v : ∀ k, epsR R ⟶ (C k).A) (B : Out.PolAV (Sp R)) (ψ : ∀ k, (C k).A ⟶ B.A) (χ : ∀ k, B.A ⟶ (C k).A) (G : Over (Sp V)) [GrpObj G] (π : G.left ⟶ B.A.left), B.g = n → (∀ k, IsLieBasis ![v k]) → (∀ k, IsMonHom (ψ k)) → (∀ k, IsMonHom (χ k)) → (∀ k, ψ k ≫ χ k = 𝟙 (C k).A ^ N) → (∀ k k', k ≠ k' → ψ k ≫ χ k' = 1) → IsUnit (N : V) → IsGrpPullback G B.A (spMap f) π → ∃ u : Fin n → (epsAt (𝟙 (Sp V)) ⟶ G), (∀ k, (u k).left ≫ π = spMap (dualMap f) ≫ (v k).left ≫ (ψ k).left) ∧ (∀ k, IsTanAt G _ (u k)) ∧ ∀ w, IsTanAt G _ w → ∃! cc : Fin n → V, IsComb cc u w := by
  intro R V _ _ _ f n N C v B ψ χ G _ π hg hv hψ hχ hpc hpo hN hpb
  obtain ⟨EBR, _, _, ⟨MBR⟩⟩ := lieModel_exists (Sp R) B.A R (𝟙 (Sp R))
  obtain ⟨EBV, _, _, ⟨MBV⟩⟩ := lieModel_exists (Sp R) B.A V (spMap f ≫ 𝟙 (Sp R))
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear (Sp R) B.A R V f (𝟙 _) EBR EBV MBR MBV
  have hx : spMap f ≫ 𝟙 (Sp R) = 𝟙 (Sp V) ≫ spMap f := by simp
  obtain ⟨MG, hMG⟩ := (GlobalTheory.T.lie_model_pullback_equivalence (Sp R) (Sp V) B.A G (spMap f) π hpb V (𝟙 (Sp V)) EBV).1 (castM hx MBV)
  have hMG' : ∀ e, (MG.pt e).left ≫ π = (MBV.pt e).left := fun e => (hMG e).trans (castM_left hx MBV e)

  have hvt : ∀ k, IsTanAt B.A (𝟙 (Sp R)) (toAt (v k) ≫ ψ k) := fun k => by
    haveI := hψ k; exact tan_comp _ (toAt_tan (v k) ((hv k).1 0)) (ψ k)
  choose eR heR using fun k => MBR.onto _ (hvt k)
  let EV : Fin n → EBV := fun k => j (eR k)
  have hlift : ∀ e, (MBV.pt (j e)).left = spMap (dualMap f) ≫ (MBR.pt e).left := fun e =>
    (Category.comp_id (MBV.pt (j e)).left).symm.trans (hj e)
  have hEV : ∀ k, (MBV.pt (EV k)).left = spMap (dualMap f) ≫ (v k).left ≫ (ψ k).left := fun k => by
    show (MBV.pt (j (eR k))).left = _
    rw [hlift, heR, Over.comp_left, toAt_left]

  choose EC iC mC MC bC hbC using fun k => lc (C k) (v k) (hv k) V f
  have hd : ∀ k, ∃ A : EBV →ₗ[V] EC k, ∀ e, (MC k).pt (A e) = MBV.pt e ≫ χ k := fun k => by
    haveI := hχ k
    exact (GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_diff (Sp R) B.A (C k).A V (spMap f ≫ 𝟙 (Sp R)) EBV (EC k) MBV (MC k) (χ k)).exists
  choose dχ hdχ using hd
  let fV : Fin n → (EBV →ₗ[V] V) := fun k => ((bC k).coord 0).comp (dχ k)
  have hval : ∀ i k, fV k (EV i) = if i = k then (N : V) else 0 := by
    intro i k
    have hleft : ((MC k).pt (dχ k (EV i))).left = spMap (dualMap f) ≫ (v i).left ≫ (ψ i ≫ χ k).left := by
      rw [hdχ, Over.comp_left, hEV, Over.comp_left]; simp only [Category.assoc]
    split_ifs with hik
    · subst hik
      have e2 : dχ i (EV i) = (N : V) • bC i 0 := by
        apply (MC i).inj
        apply Over.OverMorphism.ext
        rw [hleft, hpc, (MC i).smul, hbC, pow_left (v i) (hv i) N, ← Category.assoc, bc_eps, Category.assoc]
      simp [fV, e2]
    · have e2 : dχ k (EV i) = 0 := by
        apply (MC k).inj
        apply Over.OverMorphism.ext
        rw [hleft, hpo i k hik, pt_zero, ← bc_one f]
        congr 1
        rw [← Over.comp_left, MonObj.comp_one]
      simp [fV, e2]
  obtain ⟨bB⟩ := GlobalTheory.T.lie_model_free_of_smooth (Sp R) B.A n (hg ▸ B.smoothDim) V (spMap f ≫ 𝟙 (Sp R)) EBV MBV
  obtain ⟨hli, hsp⟩ := GlobalTheory.T.dual_family_is_basis V EBV n bB EV fV (N : V) hN hval
  have bridge := (GlobalTheory.T.lie_model_eigenvectors_action (Sp V) V G (𝟙 (Sp V)) EBV MG).1 n
  refine ⟨fun k => MG.pt (EV k), fun k => hMG' (EV k) ▸ hEV k, fun k => MG.tan _, fun w hw => ?_⟩
  obtain ⟨e, rfl⟩ := MG.onto w hw
  have hmem : e ∈ Submodule.span V (Set.range EV) := hsp ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 hmem
  refine ⟨c, (bridge c EV _).2 (by rw [hc]), fun c' hc' => ?_⟩
  have h1 := MG.inj ((bridge c' EV _).1 hc')
  rw [← hc] at h1
  have h2 := Fintype.linearIndependent_iff.1 hli (c' - c) (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h1, sub_self])
  funext i
  have := h2 i
  rw [Pi.sub_apply, sub_eq_zero] at this
  exact this
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackProductFrame

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ggeo.IntBasis

theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  simp [spMap, ← Spec.map_comp]

theorem dualMap_comp_alt {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    (dualMap b).comp (dualMap a) = dualMap (b.comp a) := by
  apply RingHom.ext
  intro x
  apply TrivSqZeroExt.ext <;> simp only [RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero, add_zero, zero_add]

end GlobalTheory.CompanionTheory.Ggeo.IntBasis

open GlobalTheory.CompanionTheory.Ggeo.IntBasis in

theorem _root_.GlobalTheory.CompanionTheory.Relay.cm_pack_product_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (N : ℕ) (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))) (V : Subring X.K) [IsLocalRing V], 0 < N → (∀ y : (FU.Di i).La, N • y ∈ Submodule.span (OK H) (Set.range fun k => (a k : (FU.Di i).La))) → (∀ s : 𝓞 X.K, (s : X.K) ∈ V) → IsUnit (N : V) → ∃ (T : SAB H (Sp V)) (m'' : SABMap X.t T (spMap (algebraMap V X.K))) (uV : Fin g → (epsAt (𝟙 (Sp V)) ⟶ T.G)), (∀ k, IsTanAt T.G _ (uV k)) ∧ (∀ w, IsTanAt T.G _ w → ∃! cc : Fin g → V, IsComb cc uV w) ∧ ∀ k u, X.IsImage (b k) (a k) u → ∃ s : Sp (DualNumber X.K) ⟶ X.t.G.left, s ≫ X.m.φ = u.left ∧ s ≫ m''.φ = spMap (dualMap (algebraMap V X.K)) ≫ (uV k).left := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X N b a V _ hN hspan hV hNu
  classical
  let f : 𝓞 X.K →+* V := (algebraMap (𝓞 X.K) X.K).codRestrict V hV
  have hf : (algebraMap V X.K).comp f = algebraMap (𝓞 X.K) X.K := by ext; rfl
  obtain ⟨T', m0, hg⟩ := GlobalTheory.CM.PAT.exists_pullback E H _ _ (spMap f) X.B
  have hψ : ∀ k, IsMonHom (X.ψ (b k) (a k)) := fun k => ((X.fam (b k)).1 (a k)).isMonHom
  obtain ⟨hon, hker⟩ := GlobalTheory.CompanionTheory.Relay.cm_pack_torsion_points E H D l Xo c g ty FU i Z P hP X N b a hN hspan
  obtain ⟨χ, hχ, hψχ, hoff⟩ := GlobalTheory.T.isogeny_product_decomposition X.K (algebraMap X.K ℂ) g N (fun k => (X.C (b k)).P) X.B.pol
    (fun k => X.ψ (b k) (a k)) hψ hN hon hker
  obtain ⟨uV, huV, htan, hbasis⟩ := GlobalTheory.CompanionTheory.Relay.isogeny_decomposition_product (𝓞 X.K) V f g N (fun k => (X.C (b k)).P) (fun k => (X.C (b k)).v)
    X.B.pol (fun k => X.ψ (b k) (a k)) χ T'.t.G m0.φ X.dim (fun k => (X.C (b k)).basis) hψ hχ hψχ hoff hNu m0.cart
  have hy : spMap (algebraMap V X.K) ≫ spMap f = spMap (algebraMap (𝓞 X.K) X.K) := by rw [spectrumMap_comp, hf]
  obtain ⟨m'', hm''⟩ := (GlobalTheory.CM.Factor.ellMap_cancel_and_sabMap_cancel E H (𝓞 X.K) V X.K f (algebraMap V X.K)).2
    (Sp (𝓞 X.K)) (spMap f) (spMap (algebraMap (𝓞 X.K) X.K)) X.B.t T'.t X.t m0 X.m' hy
  refine ⟨T'.t, m'', uV, htan, hbasis, fun k u hu => ?_⟩
  obtain ⟨r, hr1, hr2⟩ := hu
  refine ⟨r, hr1, ?_⟩
  apply m0.cart.1.hom_ext
  · rw [Category.assoc, hm'', hr2, Category.assoc, huV k]
    simp only [← Category.assoc]
    congr 2
    rw [spectrumMap_comp, dualMap_comp_alt, hf]
  · have w1 := m''.cart.1.w
    have w2 := X.m'.cart.1.w
    have hmono : Mono (spMap (algebraMap (𝓞 X.K) X.K)) := by
      have : Epi (CommRingCat.ofHom (algebraMap (𝓞 X.K) X.K)) := IsLocalization.epi (nonZeroDivisors (𝓞 X.K)) X.K
      exact (inferInstance : Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap (𝓞 X.K) X.K)).op))
    have hbase : r ≫ X.t.G.hom = spMap (algebraMap X.K (DualNumber X.K)) := by
      apply hmono.right_cancellation
      rw [Category.assoc, ← w2, ← Category.assoc, hr2]
      simp only [Category.assoc]
      rw [Over.w (X.ψ (b k) (a k)), Over.w ((X.C (b k)).v)]
      simp only [Over.mk_hom, spectrumMap_comp]
      congr 1
      ext x <;> simp only [RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero, add_zero, zero_add]
    rw [Category.assoc, w1, ← Category.assoc, hbase, Category.assoc, Over.w (uV k)]
    simp only [Over.mk_hom, Category.comp_id]
    show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
    rw [spectrumMap_comp, spectrumMap_comp]
    congr 1
    ext x <;> simp only [RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero, add_zero, zero_add]
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackProductFrameStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.cm_pack_product_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (N : ℕ) (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))) (V : Subring X.K) [IsLocalRing V], 0 < N → (∀ y : (FU.Di i).La, N • y ∈ Submodule.span (OK H) (Set.range fun k => (a k : (FU.Di i).La))) → (∀ s : 𝓞 X.K, (s : X.K) ∈ V) → IsUnit (N : V) → ∃ (T : SAB H (Sp V)) (m'' : SABMap X.t T (spMap (algebraMap V X.K))) (uV : Fin g → (epsAt (𝟙 (Sp V)) ⟶ T.G)), (∀ k, IsTanAt T.G _ (uV k)) ∧ (∀ w, IsTanAt T.G _ w → ∃! cc : Fin g → V, IsComb cc uV w) ∧ ∀ k u, X.IsImage (b k) (a k) u → ∃ s : Sp (DualNumber X.K) ⟶ X.t.G.left, s ≫ X.m.φ = u.left ∧ s ≫ m''.φ = spMap (dualMap (algebraMap V X.K)) ≫ (uV k).left := by
  first | exact @GlobalTheory.CompanionTheory.Relay.cm_pack_product_frame | exact GlobalTheory.CompanionTheory.Relay.cm_pack_product_frame | (intros; apply GlobalTheory.CompanionTheory.Relay.cm_pack_product_frame <;> assumption)
end
end
