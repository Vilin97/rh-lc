module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRaynaudTangentInvariantFields
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivPolarizationRaynaudEqPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRayQuotient
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFieldsCechH1Relation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCoboundaryOfMixedOverlapsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativesCoboundaryCoeffsMemMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudCechRelationDlogDescendsToAbelianPart

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Heat.AbDescent

theorem pbT_id {X : Scheme.{0}} {U V : X.Opens} (hV : V ≤ U) (s : Γ(X, U)) : pbT (𝟙 X) s V = rsT s V := by
  rw [GlobalTheory.KS.pbT_of_le (𝟙 X) hV, GlobalTheory.KS.rsT_of_le hV]
  simp [Scheme.Hom.appLE, resG]
  rfl

theorem pbT_pbT_id {Z X : Scheme.{0}} (q : Z ⟶ X) {U V : X.Opens} (hV : V ≤ U) {W : Z.Opens} (hW : W ≤ q ⁻¹ᵁ V)
    (s : Γ(X, U)) : pbT q (pbT (𝟙 X) s V) W = pbT q s W := by
  rw [pbT_id hV, GlobalTheory.KS.pbT_rsT q hV hW]

theorem descent : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (δH : Fld Y.H.left) (δ : Fld Q.P.A.left), (∀ (U : Q.P.A.left.Opens) (s : Γ(Q.P.A.left, U)) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ U → δH W (pbT Y.q.left s W) = pbT Y.q.left (δ U s) W) → ∀ (K : Type) (Wk : K → Y.H.left.Opens) (jk : K → Q.P.L.ι), (∀ k, ∃ V : Q.P.A.left.Opens, Wk k = Y.q.left ⁻¹ᵁ V) → ⨆ k, Wk k = ⊤ → (∀ k, Wk k ≤ Y.q.left ⁻¹ᵁ Q.P.L.U (jk k)) → ∀ (P : ∀ k, Γ(Y.H.left, Wk k)), (∀ k, IsWt Y 0 _ (P k)) → (∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → rsT (P k') Wo - rsT (P k) Wo = dlg Y.H Y.q.left Q.P.L δH (jk k) (jk k') Wo) → ∃ (V : K → Q.P.A.left.Opens) (b : ∀ k, Γ(Q.P.A.left, V k)), ⨆ k, V k = ⊤ ∧ (∀ k, V k ≤ Q.P.L.U (jk k)) ∧ ∀ k k', rsT (b k') (V k ⊓ V k') - rsT (b k) (V k ⊓ V k') = dlg Q.P.A (𝟙 _) Q.P.L δ (jk k) (jk k') (V k ⊓ V k') := by
  intro R _ _ Q O _ _ _ oa Y δH δ hpb K Wk jk hV hcov hle P hP hrel
  have := Y.smooth_q
  have := (AbConst.surjective_q Y).1
  choose V hV using hV
  have hb : ∀ k, ∃ b : Γ(Q.P.A.left, V k), pbT Y.q.left b (Wk k) = P k := by
    intro k
    have key : ∀ (W : Y.H.left.Opens) (hW : W = Y.q.left ⁻¹ᵁ V k) (p : Γ(Y.H.left, W)), IsWt Y 0 W p →
        ∃ b : Γ(Q.P.A.left, V k), pbT Y.q.left b W = p := by
      intro W hW p hp
      subst hW
      obtain ⟨a, ha⟩ := AbConst.exists_app_eq Y hp
      exact ⟨a, by rw [GlobalTheory.KS.pbT_of_le _ le_rfl, ← ha, Scheme.Hom.app_eq_appLE]⟩
    exact key _ (hV k) _ (hP k)
  choose b hb using hb
  have hVle : ∀ k, V k ≤ Q.P.L.U (jk k) := by
    intro k y hy
    obtain ⟨x, rfl⟩ := Y.q.left.surjective y
    have hx : x ∈ Wk k := by rw [hV k]; exact hy
    exact hle k hx
  refine ⟨V, b, ?_, hVle, ?_⟩
  · rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := Y.q.left.surjective y
    have hx : x ∈ ⨆ k, Wk k := by rw [hcov]; trivial
    rw [TopologicalSpace.Opens.mem_iSup] at hx ⊢
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, by rw [hV k] at hk; exact hk⟩
  · intro k k'
    have hWo : Y.q.left ⁻¹ᵁ (V k ⊓ V k') ≤ Wk k ⊓ Wk k' := by
      rw [hV k, hV k']
      exact fun x hx => ⟨hx.1, hx.2⟩
    have h := hrel k k' _ hWo
    apply FunDescent.app_injective Y.q.left (V k ⊓ V k')
    have e : ∀ s : Γ(Q.P.A.left, V k ⊓ V k'),
        (Y.q.left.app (V k ⊓ V k')).hom s = pbT Y.q.left s (Y.q.left ⁻¹ᵁ (V k ⊓ V k')) := fun s => by
      rw [GlobalTheory.KS.pbT_of_le _ le_rfl, Scheme.Hom.app_eq_appLE]
    rw [e, e, GlobalTheory.KS.pbT_sub, GlobalTheory.KS.pbT_rsT _ inf_le_right le_rfl, GlobalTheory.KS.pbT_rsT _ inf_le_left le_rfl]
    have hbk : ∀ j, Y.q.left ⁻¹ᵁ (V k ⊓ V k') ≤ Wk j →
        pbT Y.q.left (b j) (Y.q.left ⁻¹ᵁ (V k ⊓ V k')) = rsT (P j) (Y.q.left ⁻¹ᵁ (V k ⊓ V k')) := by
      intro j hj
      rw [← hb j, GlobalTheory.KS.rsT_pbT _ (hV j).le hj]
    rw [hbk k' (hWo.trans inf_le_right), hbk k (hWo.trans inf_le_left), h]
    have hUo : V k ⊓ V k' ≤ Q.P.L.U (jk k) ⊓ Q.P.L.U (jk k') := inf_le_inf (hVle k) (hVle k')
    unfold dlg
    rw [GlobalTheory.KS.pbT_mul, ← hpb (V k ⊓ V k') (pbT (𝟙 _) (Q.P.L.g (jk k) (jk k')).val (V k ⊓ V k')) _ le_rfl,
      pbT_pbT_id _ hUo le_rfl, pbT_pbT_id _ hUo le_rfl]

end GlobalTheory.Heat.AbDescent
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudCechRelationDlogDescendsToAbelianPartStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.raynaud_cech_relation_dlog_descends_to_abelian_part : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (δH : Fld Y.H.left) (δ : Fld Q.P.A.left), (∀ (U : Q.P.A.left.Opens) (s : Γ(Q.P.A.left, U)) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ U → δH W (pbT Y.q.left s W) = pbT Y.q.left (δ U s) W) → ∀ (K : Type) (Wk : K → Y.H.left.Opens) (jk : K → Q.P.L.ι), (∀ k, ∃ V : Q.P.A.left.Opens, Wk k = Y.q.left ⁻¹ᵁ V) → ⨆ k, Wk k = ⊤ → (∀ k, Wk k ≤ Y.q.left ⁻¹ᵁ Q.P.L.U (jk k)) → ∀ (P : ∀ k, Γ(Y.H.left, Wk k)), (∀ k, IsWt Y 0 _ (P k)) → (∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → rsT (P k') Wo - rsT (P k) Wo = dlg Y.H Y.q.left Q.P.L δH (jk k) (jk k') Wo) → ∃ (V : K → Q.P.A.left.Opens) (b : ∀ k, Γ(Q.P.A.left, V k)), ⨆ k, V k = ⊤ ∧ (∀ k, V k ≤ Q.P.L.U (jk k)) ∧ ∀ k k', rsT (b k') (V k ⊓ V k') - rsT (b k) (V k ⊓ V k') = dlg Q.P.A (𝟙 _) Q.P.L δ (jk k) (jk k') (V k ⊓ V k') := by
  first | exact @GlobalTheory.Heat.AbDescent.descent | exact GlobalTheory.Heat.AbDescent.descent | (intros; apply GlobalTheory.Heat.AbDescent.descent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorEqZeroOfLogDerivCoboundary

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LieRigid

open GlobalTheory.ZH.CrdCalc (valR_res valR_spMap valR_eq valHom)

theorem dlg_sub {A : Type} [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left)
    (δ : Fld B.left) (hδ : IsField ⊤ δ) (i j : L.ι) {O T : B.left.Opens} (hO : O ≤ L.U i ⊓ L.U j) (hT : T ≤ O) :
    rsT (dlg B (𝟙 _) L δ i j O) T = rsT (dlg B (𝟙 _) L δ i j (L.U i ⊓ L.U j)) T := by
  rw [GlobalTheory.CoverRefinementPullback.dlg_res' B L δ hδ i j (hT.trans hO)]
  unfold dlg
  rw [GlobalTheory.KS.rsT_of_le hT, map_mul, GlobalTheory.CoverRefinementPullback.pbT_id' _ hO, GlobalTheory.CoverRefinementPullback.pbT_id' _ hO, ← hδ.2.2 _ _ hT le_top,
    GlobalTheory.CoverRefinementPullback.resG_resG', GlobalTheory.CoverRefinementPullback.resG_resG']
  rfl

theorem lie_inj : ∀ (R : Type) [CommRing R] [IsLocalRing R] (P : PolAV (Sp R)) (w : TanM (𝟙 (Sp R)) P.A) (δ : Fld P.A.left), IsInv P.A w δ → ∀ (K : Type) (V : K → P.A.left.Opens) (jk : K → P.L.ι), ⨆ k, V k = ⊤ → (∀ k, V k ≤ P.L.U (jk k)) → ∀ (b : ∀ k, Γ(P.A.left, V k)), (∀ k k', rsT (b k') (V k ⊓ V k') - rsT (b k) (V k ⊓ V k') = dlg P.A (𝟙 _) P.L δ (jk k) (jk k') (V k ⊓ V k')) → w = 0 := by
  intro R _ _ P w δ hδ K V jk hV hVj b hb
  have hδ1 : IsField ⊤ δ := hδ.1
  have hcob : IsCob P.L.U (fun j j' => dlg P.A (𝟙 _) P.L δ j j' (P.L.U j ⊓ P.L.U j')) := by
    refine GlobalTheory.T.isCechOneCoboundary_of_mixed_overlaps P.A.left P.L.ι K P.L.U V hV _
      (fun k k' => dlg P.A (𝟙 _) P.L δ (jk k) (jk k') (V k ⊓ V k'))
      (fun j k => rsT (dlg P.A (𝟙 _) P.L δ j (jk k) (P.L.U j ⊓ P.L.U (jk k))) (P.L.U j ⊓ V k))
      (fun j j' k => ?_) (fun j k k' => ?_) ⟨b, fun k k' => (hb k k').symm⟩
    · have t1 : P.L.U j ⊓ P.L.U j' ⊓ V k ≤ P.L.U j ⊓ P.L.U j' := inf_le_left
      have t2 : P.L.U j ⊓ P.L.U j' ⊓ V k ≤ P.L.U j ⊓ V k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
      have t3 : P.L.U j ⊓ P.L.U j' ⊓ V k ≤ P.L.U j' ⊓ V k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
      rw [GlobalTheory.KS.rsT_rsT (inf_le_inf le_rfl (hVj k)) t2, GlobalTheory.KS.rsT_rsT (inf_le_inf le_rfl (hVj k)) t3,
        ← GlobalTheory.CoverRefinementPullback.dlg_tri _ _ P.isLB δ hδ1 j j' (jk k) t1 (t3.trans (inf_le_inf le_rfl (hVj k)))
          (t2.trans (inf_le_inf le_rfl (hVj k)))]
      abel
    · have t1 : P.L.U j ⊓ V k ⊓ V k' ≤ V k ⊓ V k' := le_inf (inf_le_left.trans inf_le_right) inf_le_right
      have t2 : P.L.U j ⊓ V k ⊓ V k' ≤ P.L.U j ⊓ V k := inf_le_left
      have t3 : P.L.U j ⊓ V k ⊓ V k' ≤ P.L.U j ⊓ V k' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
      rw [dlg_sub _ _ δ hδ1 (jk k) (jk k') (inf_le_inf (hVj k) (hVj k')) t1,
        GlobalTheory.KS.rsT_rsT (inf_le_inf le_rfl (hVj k)) t2, GlobalTheory.KS.rsT_rsT (inf_le_inf le_rfl (hVj k')) t3,
        ← GlobalTheory.CoverRefinementPullback.dlg_tri _ _ P.isLB δ hδ1 j (jk k) (jk k')
          (t2.trans (inf_le_inf le_rfl (hVj k))) (t1.trans (inf_le_inf (hVj k) (hVj k')))
          (t3.trans (inf_le_inf le_rfl (hVj k')))]
      abel
  obtain ⟨H, hH⟩ := hcob

  have hgp := GlobalTheory.Heat.DlogIndep.isGrpPullback_self P.A
  obtain ⟨u, hu⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.push_surj hgp (tv w)
  have hul : u.left = (tv w).left := (Category.comp_id _).symm.trans (congrArg (fun q => q.left) hu)
  have hut : IsTangent u :=
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.isTangent_iff hgp _).2 (by rw [hu]; exact ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem _)
  have hee : ∀ (S : Type) [CommRing S] [Algebra R S] (φ : DualNumber R →ₐ[R] S),
      φ DualNumber.eps * φ DualNumber.eps = 0 := fun S _ _ φ => by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hφ : ∀ (S : Type) [CommRing S] [Algebra R S] (φ : DualNumber R →ₐ[R] S),
      (algOverHom φ ≫ u : algOver R S ⟶ P.A) = (Chart.spMap (SqZero.epsTo R (φ DualNumber.eps) (hee S φ)) ≫ u) := by
    intro S _ _ φ
    have e : φ = SqZero.epsTo R (φ DualNumber.eps) (hee S φ) := DualNumber.algHom_ext (by simp [SqZero.epsTo, SqZero.dualTo_apply])
    conv_lhs => rw [e]
    rfl
  have h1 : u = 1 := GlobalTheory.Heat.DlogIndep.eq_one_of_coboundary P.isLB P.ktriv (DualNumber.eps : DualNumber R)
    DualNumber.eps_mul_eps u (fun j => -H j)
    (fun S _ _ φ y U hU => by
      rw [hφ S φ]; exact (GlobalTheory.Heat.DlogIndep.valR_translate hul hut hδ _ (hee S φ) y U hU).1)
    (fun S _ _ φ y j j' hj hj' => by
      rw [hφ S φ]
      have hU : ⊤ ≤ y.left ⁻¹ᵁ (P.L.U j ⊓ P.L.U j') := fun p hp => ⟨hj hp, hj' hp⟩
      have e₁ := congrArg (valHom (R := S) y.left _ hU) (hH j j')
      have r₁ : valHom (R := S) y.left _ hU (rsT (H j) _) = valHom (R := S) y.left _ hj (H j) := by
        rw [rsT, dite_eq_left inf_le_left, ← valR_eq, ← valR_eq]
        exact valR_res _ _ hU _
      have r₂ : valHom (R := S) y.left _ hU (rsT (H j') _) = valHom (R := S) y.left _ hj' (H j') := by
        rw [rsT, dite_eq_left inf_le_right, ← valR_eq, ← valR_eq]
        exact valR_res _ _ hU _
      simp only [dlg, GlobalTheory.Heat.DlogIndep.pbT_id, map_sub, map_mul, r₁, r₂] at e₁
      have e₂ : valHom (R := S) y.left _ hU (P.L.g j j').val * valHom (R := S) y.left _ hU (P.L.g j j')⁻¹.val = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      refine ((GlobalTheory.Heat.DlogIndep.valR_translate hul hut hδ _ (hee S φ) y _ hU).2 _).trans ?_
      simp only [valR_eq (R := S) _ _ hU, valR_eq (R := S) _ _ hj, valR_eq (R := S) _ _ hj', map_neg]
      linear_combination (φ DualNumber.eps * valHom (R := S) y.left _ hU (P.L.g j j').val) * e₁ +
        (-(φ DualNumber.eps * valHom (R := S) y.left _ hU (δ _ (P.L.g j j').val))) * e₂)
  have h2 : tv w = tv (0 : TanM (𝟙 (Sp R)) P.A) := by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_zero, ← hu, h1, map_one]
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.tanM_ext h2

end GlobalTheory.LieRigid
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorEqZeroOfLogDerivCoboundaryStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tangentVector_eq_zero_of_logDeriv_coboundary : ∀ (R : Type) [CommRing R] [IsLocalRing R] (P : PolAV (Sp R)) (w : TanM (𝟙 (Sp R)) P.A) (δ : Fld P.A.left), IsInv P.A w δ → ∀ (K : Type) (V : K → P.A.left.Opens) (jk : K → P.L.ι), ⨆ k, V k = ⊤ → (∀ k, V k ≤ P.L.U (jk k)) → ∀ (b : ∀ k, Γ(P.A.left, V k)), (∀ k k', rsT (b k') (V k ⊓ V k') - rsT (b k) (V k ⊓ V k') = dlg P.A (𝟙 _) P.L δ (jk k) (jk k') (V k ⊓ V k')) → w = 0 := by
  first | exact @GlobalTheory.LieRigid.lie_inj | exact GlobalTheory.LieRigid.lie_inj | (intros; apply GlobalTheory.LieRigid.lie_inj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFieldCombKillsWeightZeroOfCoboundary

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatUniq

theorem comb_kills_weight_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (K : Type) (Wk : K → Y.H.left.Opens) (jk : K → Q.P.L.ι), (∀ k, ∃ V : Q.P.A.left.Opens, Wk k = Y.q.left ⁻¹ᵁ V) → ⨆ k, Wk k = ⊤ → (∀ k, Wk k ≤ Y.q.left ⁻¹ᵁ Q.P.L.U (jk k)) → ∀ (P : ∀ k, Γ(Y.H.left, Wk k)) (e : Fin n → R), (∀ k, IsWt Y 0 _ (P k)) → (∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → rsT (P k') Wo - rsT (P k) Wo = ∑ a, constFn Y.H.hom Wo (e a) * dlg Y.H Y.q.left Q.P.L (dd a) (jk k) (jk k') Wo) → ∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0 := by
  intro R _ _ _ _ _ Q O _ _ _ oa Y n v dd hinv K Wk jk hWk hcov hjk P e hP hcob V f hf
  haveI : IsMonHom Y.q := Y.q_linear.isMonHom
  obtain ⟨dw, hdw⟩ := GlobalTheory.RayBasis.exists_isInv (∑ a, e a • v a)
  obtain ⟨δ, hδ⟩ := GlobalTheory.RayBasis.exists_isInv (GlobalTheory.Heat.LiePush.pushL Y.q (∑ a, e a • v a))
  have hcomb : ∀ (W : Y.H.left.Opens) (s : Γ(Y.H.left, W)),
      dw W s = ∑ a, constFn Y.H.hom W (e a) * dd a W s := by
    intro W s
    have h := GlobalTheory.Heat.LiePush.isInv_pbT (𝟙 Y.H) hdw (w := v) hinv e
      (PullbackSections.tanM_ext (by rw [GlobalTheory.Heat.LiePush.tv_pushL]; exact Category.comp_id _)) W s W le_rfl
    simpa only [Over.id_left, GlobalTheory.Heat.LiePush.pbT_id] using h
  have hpull : ∀ (U : Q.P.A.left.Opens) (s : Γ(Q.P.A.left, U)) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ U →
      dw W (pbT Y.q.left s W) = pbT Y.q.left (δ U s) W := by
    intro U s W hW
    have h := GlobalTheory.Heat.LiePush.isInv_pbT Y.q hdw (g := 1) (w := fun _ => GlobalTheory.Heat.LiePush.pushL Y.q (∑ a, e a • v a))
      (d' := fun _ => δ) (fun _ => hδ) (fun _ => 1) (by simp) U s W hW
    have h1 : constFn Q.P.A.hom U (1 : R) = 1 := by simp [constFn]
    simpa [h1] using h
  obtain ⟨Vs, b, hVcov, hVle, hb⟩ := GlobalTheory.T.raynaud_cech_relation_dlog_descends_to_abelian_part R Q O oa Y dw δ hpull K Wk jk hWk hcov hjk P hP
    (fun k k' Wo hWo => by
      rw [hcob k k' Wo hWo]
      simp only [dlg, hcomb, Finset.sum_mul, _root_.mul_assoc])
  have hw0 : GlobalTheory.Heat.LiePush.pushL Y.q (∑ a, e a • v a) = 0 := GlobalTheory.T.tangentVector_eq_zero_of_logDeriv_coboundary R Q.P _ δ hδ K Vs jk hVcov hVle b hb
  have hδ0 : ∀ (U : Q.P.A.left.Opens) (s : Γ(Q.P.A.left, U)), δ U s = 0 := by
    intro U s
    have h := GlobalTheory.Heat.LiePush.isInv_pbT (𝟙 Q.P.A) hδ (g := 0) (w := Fin.elim0) (d' := Fin.elim0)
      (fun a => a.elim0) Fin.elim0
      (by rw [hw0, map_zero]; simp) U s U le_rfl
    simpa only [Over.id_left, GlobalTheory.Heat.LiePush.pbT_id, Finset.univ_eq_empty, Finset.sum_empty] using h
  obtain ⟨g, hg⟩ := GlobalTheory.Heat.AbConst.exists_app_eq Y hf
  have hfg : f = pbT Y.q.left g (Y.q.left ⁻¹ᵁ V) := by
    rw [← hg, GlobalTheory.KS.pbT_of_le _ le_rfl, Scheme.Hom.app_eq_appLE]
  rw [← hcomb, hfg, hpull V g _ le_rfl, hδ0, GlobalTheory.KS.pbT_zero]

end GlobalTheory.HeatUniq
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFieldCombKillsWeightZeroOfCoboundaryStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.invariantField_comb_kills_weightZero_of_coboundary : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (K : Type) (Wk : K → Y.H.left.Opens) (jk : K → Q.P.L.ι), (∀ k, ∃ V : Q.P.A.left.Opens, Wk k = Y.q.left ⁻¹ᵁ V) → ⨆ k, Wk k = ⊤ → (∀ k, Wk k ≤ Y.q.left ⁻¹ᵁ Q.P.L.U (jk k)) → ∀ (P : ∀ k, Γ(Y.H.left, Wk k)) (e : Fin n → R), (∀ k, IsWt Y 0 _ (P k)) → (∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → rsT (P k') Wo - rsT (P k) Wo = ∑ a, constFn Y.H.hom Wo (e a) * dlg Y.H Y.q.left Q.P.L (dd a) (jk k) (jk k') Wo) → ∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0 := by
  first | exact @GlobalTheory.HeatUniq.comb_kills_weight_zero | exact GlobalTheory.HeatUniq.comb_kills_weight_zero | (intros; apply GlobalTheory.HeatUniq.comb_kills_weight_zero <;> assumption)
end
end
