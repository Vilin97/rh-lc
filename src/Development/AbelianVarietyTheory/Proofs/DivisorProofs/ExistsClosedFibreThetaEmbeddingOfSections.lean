module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupNonzeroLocusEmbH
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedFibrePt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendFiniteModif
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToProjSecPullSecPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorFieldPointThroughGenericPoint
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.TorsionZeroCountTwist
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailFurther

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem LabCover.exists_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (M' : Modif R) (h : M'.S ⟶ C.S), M'.gp ≫ h = C.gp → h ≫ C.π = M'.π → ∃ (C' : LabCover D) (eS : C'.S ≅ M'.S) (β : C'.G.left ⟶ C.G.left), eS.hom ≫ M'.π = C'.π ∧ IsGrpPullback C'.G C.G (eS.hom ≫ h) β ∧ LBIso C'.P.L.L (C.P.L.L.pull β) := by
  intro R _ _ _ D C M' h hgp hπ
  have hex : ∃ (P' : GlobalTheory.UU.CP ((Over.pullback h).obj C.G)) (w : _),
      GlobalTheory.UU.IsCPMap P' C.P h (pullback.fst C.G.hom h) pullback.condition w :=
    GlobalTheory.UU.exists_pull C.P (GlobalTheory.UU.toBase_mul_pullback C.G h)
  obtain ⟨P', w, hP⟩ := hex
  have hG : IsGrpPullback ((Over.pullback h).obj C.G) C.G h (pullback.fst C.G.hom h) := isGrpPullback_pullback C.G h
  have hw : LBIso P'.L.L (C.P.L.L.pull (pullback.fst C.G.hom h)) := ⟨w, hP.gen⟩

  have key : ∀ {Y : Scheme.{0}} (b : Y ⟶ ((Over.pullback h).obj C.G).left) (c : Y ⟶ C.G.left),
      c = b ≫ pullback.fst C.G.hom h → LBIso (P'.L.L.pull b) (C.P.L.L.pull c) := fun b c e =>
    LBIso.chartPull (chartPullId _) (GlobalTheory.RigidBundleGlue.chartPullComp C.P.L.L _ b c e)
      (GlobalTheory.RigidBundleGlue.LBIso.pull hw b)
  let α' : C.A.A.left ⟶ ((Over.pullback h).obj C.G).left :=
    pullback.lift C.α (C.A.A.hom ≫ M'.gp) (by rw [C.α_cart.1.w, Category.assoc, hgp])
  have hα : α' ≫ pullback.fst C.G.hom h = C.α := pullback.lift_fst _ _ _
  refine ⟨{ toModif := M'
            G := (Over.pullback h).obj C.G
            semi := IsSemiAbelian.pullback h C.G C.semi
            P := P'
            A := C.A
            α := α'
            α_cart := IsGrpPullback.cancel hG (C.α_cart.congr hgp.symm hα.symm) (pullback.lift_snd _ _ _)
            α_lb := LBIso.trans C.A.isLB (pull_isLB C.P.L.isLB _) (pull_isLB P'.L.isLB _) C.α_lb
              (LBIso.symm (key α' C.α hα.symm))
            n := C.n
            n_prime := C.n_prime
            n_odd := C.n_odd
            n_unit := C.n_unit
            lab := C.lab
            trait := ?_ }, Iso.refl _, pullback.fst C.G.hom h, Category.id_comp _,
      hG.congr (Category.id_comp _).symm rfl, hw⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain ⟨W', _, _, _, io, G'', _, _, β, D', A', U', hD, hW', hio, hfin, hcart, hlb, hlab⟩ :=
    C.trait W hW φ (ξ ≫ h) hφ hloc (by rw [Category.assoc, hπ]; exact hξ)
  let β' : G''.left ⟶ ((Over.pullback h).obj C.G).left :=
    pullback.lift β (G''.hom ≫ spMap io ≫ ξ) (by rw [hcart.1.w, Category.assoc, Category.assoc])
  have hβ : β' ≫ pullback.fst C.G.hom h = β := pullback.lift_fst _ _ _
  refine ⟨W', inferInstance, inferInstance, inferInstance, io, G'', inferInstance, inferInstance, β', D', A', U', hD, hW',
    hio, hfin, IsGrpPullback.cancel hG (hcart.congr (Category.assoc _ _ _).symm hβ.symm) (pullback.lift_snd _ _ _),
    LBIso.trans U'.LG.isLB (pull_isLB C.P.L.isLB _) (pull_isLB P'.L.isLB _) hlb (LBIso.symm (key β' β hβ.symm)), ?_⟩
  intro F _ _ _ _ em hF j p p₁ p' x' h₁ h₂ h₃ h₄
  refine hlab F em hF j p p₁ p' x' h₁ h₂ h₃ ?_
  have e := congrArg (· ≫ pullback.fst C.G.hom h) h₄
  simp only [Category.assoc, hβ, hα] at e
  simpa only [Category.assoc] using e

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEmbHOfClosed

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb

theorem exists_trait_point {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (M : Modif R) (x : M.S)
    (hx : M.π x = closedPoint R) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (ξ : Sp W ⟶ M.S),
      GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ ≫ M.π = spMap φ ∧ ξ (closedPoint W) = x := by
  have : IsNoetherianRing R := hR.1.1
  have : CharZero R := hR.2
  have := M.proper
  have := M.integral
  have := M.dominant
  have : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (M.S.fromSpecStalk x ≫ M.π)
  have hψp : ∀ q : Spec (M.S.presheaf.stalk x), Spec.map ψ q = M.π (M.S.fromSpecStalk x q) := fun q => by
    rw [hψ, Scheme.Hom.comp_apply]
  have hloc : IsLocalHom ψ.hom := by
    rw [isLocalHom_iff_comap_closedPoint]
    have := hψp (closedPoint _)
    rw [Scheme.fromSpecStalk_closedPoint, hx] at this
    exact this

  let t₀ : Sp (FractionRing R) := closedPoint (FractionRing R)
  have hsp : M.gp t₀ ⤳ x := by
    rw [specializes_iff_mem_closure]
    have h1 : Set.range M.gp ⊆ {M.gp t₀} := by
      rintro _ ⟨t, rfl⟩
      rw [Subsingleton.elim t t₀]; rfl
    exact closure_mono h1 ((IsDominant.denseRange (f := M.gp)).closure_eq ▸ Set.mem_univ x)
  have hr : M.gp t₀ ∈ Set.range (M.S.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact hsp
  obtain ⟨q, hq⟩ := hr
  have e1 : Spec.map ψ q = jK R t₀ := by
    rw [hψp, hq, ← Scheme.Hom.comp_apply, M.gp_π]
  have h2 : Ideal.comap ψ.hom q.asIdeal = ⊥ := by
    have := congrArg (fun p : Sp R => (p : PrimeSpectrum R).asIdeal) e1
    change Ideal.comap ψ.hom q.asIdeal = Ideal.comap (algebraMap R (FractionRing R)) t₀.asIdeal at this
    rw [this, @Ideal.eq_bot_of_prime _ _ t₀.asIdeal t₀.isPrime]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
  have hinj : Function.Injective ψ.hom := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ Ideal.comap ψ.hom q.asIdeal := by
      rw [Ideal.mem_comap, ha]; exact q.asIdeal.zero_mem
    rw [h2] at this
    exact this
  have : CharZero (M.S.presheaf.stalk x) := charZero_of_injective_ringHom hinj
  have key : ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (χ : M.S.presheaf.stalk x →+* W),
      GlobalTheory.LN.CDvr W ∧ Function.Injective χ ∧ IsLocalHom χ := by
    by_cases h : IsField (M.S.presheaf.stalk x)
    · letI := h.toField
      refine ⟨PowerSeries (M.S.presheaf.stalk x), inferInstance, inferInstance, inferInstance, PowerSeries.C,
        ⟨inferInstance, ?_, ?_⟩, PowerSeries.C_injective, inferInstance⟩
      · rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
      · exact charZero_of_injective_ringHom (f := PowerSeries.C (R := M.S.presheaf.stalk x)) (RingHom.injective _)
    · obtain ⟨O, _, _, _, _, χ, h1, h2⟩ := GlobalTheory.exists_complete_discreteValuationRing_dominating _ h
      have : CharZero O := charZero_of_injective_ringHom h1
      exact ⟨O, inferInstance, inferInstance, inferInstance, χ, ⟨inferInstance, inferInstance, inferInstance⟩, h1, h2⟩
  obtain ⟨W, _, _, _, χ, hW, hχ, hχl⟩ := key
  refine ⟨W, inferInstance, inferInstance, inferInstance, χ.comp ψ.hom, Spec.map (CommRingCat.ofHom χ) ≫ M.S.fromSpecStalk x,
    hW, hχ.comp hinj, RingHom.isLocalHom_comp _ _, ?_, ?_⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp]; rfl
  · exact (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (M.S.fromSpecStalk x) (IsLocalRing.comap_closedPoint χ)) Scheme.fromSpecStalk_closedPoint)

end GlobalTheory.Mum.SecEmb

namespace GlobalTheory.Mum.SecEmb

theorem mem_embH_of_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (G : Over M.S) [GrpObj G],
    IsSemiAbelian G → ∀ (B L : LB G.left), B.IsLB → L.IsLB → ∀ (N : ℕ) (s : Fin (N + 1) → B.Sec) (θ : L.Sec)
    (Y : Over (Sp (ResidueField R))) [GrpObj Y], Smooth Y.hom → ∀ (j : Y.left ⟶ PSpace R N),
    j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R) → IsImmersion j → ∀ (O : Y.left.Opens),
    GlobalTheory.Mum.SecEmb.TraitRed M G s θ Y j O →
    ∀ g : G.left, M.π (G.hom g) = closedPoint R → g ∈ GlobalTheory.Mum.SecEmb.embH s := by
  intro R _ _ _ hR M G _ _ B L _ _ N s θ Y _ _ j _ _ O hT g hg
  obtain ⟨W, _, _, _, φ, ξ, hW, hφ, hl, hξ, hξx⟩ := exists_trait_point hR M (G.hom g) hg
  obtain ⟨W', _, _, _, io, G', _, β, κ, e, hW', hio, hfin, hcart, -, -, hpts⟩ := hT W hW φ ξ hφ hl hξ
  have hiol : IsLocalHom io := by
    letI := io.toAlgebra
    have : Module.Finite W W' := hfin
    have : FaithfulSMul W W' := (faithfulSMul_iff_algebraMap_injective W W').2 hio
    exact (inferInstance : IsLocalHom (algebraMap W W'))
  have hc : (spMap io ≫ ξ) (closedPoint W') = G.hom g :=
    (Scheme.Hom.comp_apply _ _ _).trans ((congrArg ξ (IsLocalRing.comap_closedPoint io)).trans hξx)
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := spMap io ≫ ξ) g
    (closedPoint W') hc.symm
  have hg1 : β (hcart.1.isoPullback.inv z) = g := by
    rw [← Scheme.Hom.comp_apply, hcart.1.isoPullback_inv_fst, hz1]
  have hg2 : G'.hom (hcart.1.isoPullback.inv z) = closedPoint W' := by
    rw [← Scheme.Hom.comp_apply, hcart.1.isoPullback_inv_snd, hz2]
  obtain ⟨q, hq1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G'.hom) (g := spMap (residue W'))
    (hcart.1.isoPullback.inv z) (closedPoint (ResidueField W'))
    (hg2.trans (IsLocalRing.comap_closedPoint (residue W')).symm)
  let F := ((Over.pullback (spMap (residue W'))).obj G').left
  let q' : F := q
  obtain ⟨⟨hs, -⟩, -⟩ := hpts (F.residueField q') (F.fromSpecResidueField q')
    (F.fromSpecResidueField q' ≫ pullback.fst G'.hom (spMap (residue W')))
    (F.fromSpecResidueField q' ≫ e.hom.left ≫ pullback.fst Y.hom (spMap κ)) rfl rfl
  have hm : closedPoint (F.residueField q') ∈
      ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) ((F.fromSpecResidueField q' ≫ pullback.fst G'.hom (spMap (residue W'))) ≫ β)) := by
    rw [hs]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  rw [GlobalTheory.nonzeroLocus_secPull] at hi
  have hpt : ((F.fromSpecResidueField q' ≫ pullback.fst G'.hom (spMap (residue W'))) ≫ β)
      (closedPoint (F.residueField q')) = g := by
    have h1 : (F.fromSpecResidueField q' ≫ pullback.fst G'.hom (spMap (residue W'))) (closedPoint (F.residueField q')) =
        hcart.1.isoPullback.inv z :=
      (Scheme.Hom.comp_apply _ _ _).trans
        ((congrArg (pullback.fst G'.hom (spMap (residue W'))) (Scheme.fromSpecResidueField_apply q' _)).trans hq1)
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg β h1).trans hg1)
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
  rw [← hpt]
  exact hi

end GlobalTheory.Mum.SecEmb
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitRedCover

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb

theorem sec_eq_of_inj {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {s s' : LB.Sec (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (hinj : ∀ W : Y.Opens, Function.Injective (h.app W).hom)
    (H : ∀ y J, Good L y J → sval s (𝟙 Y' ≫ h) y J = sval s' (𝟙 Y' ≫ h) y J) : s = s' := by
  have e : ∀ j, s.f j = s'.f j := fun j => by
    refine hinj _ (fn_ext fun y hy => ?_)
    choose J hJ using fun ψ : Y' ⟶ X => exists_chart hL (ψ y)
    have hJ' : Good L y J := hJ
    have hy' : (𝟙 Y' ≫ h) y ∈ LB.wchart L φ j := hy
    have m := hJ'.mem φ (𝟙 Y' ≫ h)
    refine (gs_pull (𝟙 Y') h y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') h y _ hy _).symm)
    exact (sec_trans s _ y hy' m).trans ((congrArg _ (H y J hJ')).trans (sec_trans s' _ y hy' m).symm)
  cases s
  cases s'
  congr
  exact funext e

end GlobalTheory.Mum.SecEmb

namespace GlobalTheory.Mum.SecEmb

theorem traitRed_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C C' : LabCover D) (Sc : Secs C.toModif C.G C.P.L.L C.α) (h : C'.S ⟶ C.S) (β : C'.G.left ⟶ C.G.left),
    h ≫ C.π = C'.π → IsGrpPullback C'.G C.G h β → LBIso C'.P.L.L (C.P.L.L.pull β) →
    ∀ σ : Fin (Sc.N + 1) → SecK C.P.L.L β Sc.k, (∀ i, Agree C.P.L.L (σ i) (Sc.s i)) →
    ∀ θ₀ : SecK C.P.L.L β 1, Agree C.P.L.L θ₀ Sc.θ →
    ∃ θ : C'.P.L.L.Sec, GlobalTheory.Mum.SecEmb.TraitRed C'.toModif C'.G σ θ Sc.Y Sc.j Sc.O := by
  intro R _ _ _ _ D C C' Sc h β hπ hpb hiso σ hσ θ₀ hθ₀
  have hL : C.P.L.L.IsLB := C.P.L.isLB
  obtain ⟨θ₁, hθ₁⟩ := exists_sec hL (φ := fun _ : Fin 1 => β) (ε := fun _ => ((1 : ℕ) : ℤ))
    (φ' := fun _ : PUnit => β) (ε' := fun _ => 1) (fun U _ g => by simp) θ₀
  obtain ⟨w, hw⟩ := hiso
  refine ⟨DVR.secOfIso (u := w) θ₁ hw C'.P.L.isLB (LB.isLB_pull hL β), ?_⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain ⟨W', _, _, _, io, G'', _, β'', σ'', θ'', κ, e, hW', hio, hfin, hG'', hκ, he, hσ'', hθ'', hfib⟩ :=
    Sc.trait W hW φ (ξ ≫ h) hφ hloc (by rw [Category.assoc, hπ]; exact hξ)
  obtain ⟨β', hβ'1, hβ'2⟩ : ∃ β' : G''.left ⟶ C'.G.left, β' ≫ β = β'' ∧ β' ≫ C'.G.hom = G''.hom ≫ spMap io ≫ ξ :=
    ⟨hpb.1.lift β'' (G''.hom ≫ spMap io ≫ ξ) (by rw [hG''.1.w]; simp), hpb.1.lift_fst _ _ _, hpb.1.lift_snd _ _ _⟩
  subst hβ'1

  have hρ : Function.Injective ((algebraMap W' (FractionRing W')).comp (io.comp φ)) :=
    (IsFractionRing.injective W' (FractionRing W')).comp (hio.comp hφ)
  obtain ⟨ga, -, hga⟩ := Modif.factor_gp R C.toModif (FractionRing W') _ (jK W' ≫ spMap io ≫ ξ ≫ h) hρ (by
    rw [Category.assoc, Category.assoc, Category.assoc, hπ, hξ]
    simp only [jK, spMap, ← Spec.map_comp]
    rfl)

  have : Smooth C.G.hom := C.semi.smooth
  have : Flat G''.hom := MorphismProperty.of_isPullback (P := @Flat) hG''.1 inferInstance

  have hgen : ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback G''.hom (jK W')), ∃ q : Z ⟶ C.A.A.left,
      q ≫ C.α = r ≫ pullback.fst G''.hom (jK W') ≫ β' ≫ β := fun Z r => by
    refine ⟨C.α_cart.1.lift (r ≫ pullback.fst G''.hom (jK W') ≫ β' ≫ β)
      (r ≫ pullback.snd G''.hom (jK W') ≫ spMap ga) ?_, C.α_cart.1.lift_fst _ _ _⟩
    have w₁ := hG''.1.w
    simp only [Category.assoc] at w₁ ⊢
    rw [w₁, ← hga, pullback.condition_assoc]

  have key : ∀ {n : ℕ} (a : SecK C.P.L.L (β' ≫ β) n) (b : SecK C.P.L.L β n) (c : SecK C.P.L.L C.α n),
      Agree C.P.L.L a c → Agree C.P.L.L b c → ∀ (Z : Scheme.{0}) (r : Z ⟶ G''.left) (z : Z) (J), Good C.P.L.L z J →
        sval a r z J = sval b (r ≫ β') z J := by
    intro n a b c ha hb
    have e₁ : a = ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec b β' := by
      refine sec_eq_of_inj hL (GlobalTheory.ExpInt.generic_app_injective G'') fun y J hJ => ?_
      rw [ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ]
      obtain ⟨q, hq⟩ := hgen _ (𝟙 _)
      have hq' : q ≫ C.α = (𝟙 _ ≫ pullback.fst G''.hom (jK W')) ≫ β' ≫ β := by rw [hq]; simp
      refine (ha _ _ q hq'.symm y J hJ).trans (hb _ _ q ?_ y J hJ).symm
      rw [hq']; simp
    intro Z r z J hJ
    rw [e₁, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ]
  have hv : ∀ i (Z : Scheme.{0}) (r : Z ⟶ G''.left) (z : Z) (J), Good C.P.L.L z J →
      sval (σ'' i) r z J = sval (σ i) (r ≫ β') z J := fun i => key _ _ _ (hσ'' i) (hσ i)
  have hvθ := key _ _ _ hθ'' hθ₀
  refine ⟨W', inferInstance, inferInstance, inferInstance, io, G'', inferInstance, β', κ, e, hW', hio, hfin,
    IsGrpPullback.cancel hpb (by rw [Category.assoc]; exact hG'') hβ'2, hκ, he, ?_⟩
  intro Ω _ p p' y hp hy
  obtain ⟨⟨hs, hproj⟩, hnz⟩ := hfib Ω p p' y hp hy
  have hnzi : ∀ (x : Sp Ω) i, p' x ∈ nonzeroLocus (σ'' i) ↔ (p' ≫ β') x ∈ nonzeroLocus (σ i) := fun x i => by
    choose J hJ using fun ψ : Sp Ω ⟶ C.G.left => exists_chart hL (ψ x)
    rw [GlobalTheory.TwistZero.mem_nonzeroLocus_iff _ _ _ hJ, GlobalTheory.TwistZero.mem_nonzeroLocus_iff _ _ _ hJ, hv i _ _ _ _ hJ]
  have ht : ⨆ i, nonzeroLocus (GlobalTheory.secPull (σ i) (p' ≫ β')) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs.ge (Set.mem_univ x))
    rw [GlobalTheory.nonzeroLocus_secPull] at hi
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
    rw [GlobalTheory.nonzeroLocus_secPull]
    exact (hnzi x i).1 hi
  refine ⟨⟨ht, ?_⟩, fun x hx => ?_⟩
  · rw [← hproj]
    refine GlobalTheory.ProjSpace.toProj_eq_of_locally hs ht fun x => ?_
    obtain ⟨c, hc⟩ := exists_chart hL ((p' ≫ β' ≫ β) x)
    have m₁ : x ∈ (LB.pull (LB.LinComb C.P.L.L (fun _ : Fin 1 => β' ≫ β) (fun _ => (Sc.k : ℤ))) p').U
        (fun _ => fun _ => c) :=
      mem_pull.2 (Set.mem_iInter.2 fun _ => by simpa using hc)
    have m₂ : x ∈ (LB.pull (LB.LinComb C.P.L.L (fun _ : Fin 1 => β) (fun _ => (Sc.k : ℤ))) (p' ≫ β')).U
        (fun _ => fun _ => c) :=
      mem_pull.2 (Set.mem_iInter.2 fun _ => by simpa using hc)
    refine ⟨(LB.pull (LB.LinComb C.P.L.L (fun _ : Fin 1 => β' ≫ β) (fun _ => (Sc.k : ℤ))) p').U (fun _ => fun _ => c) ⊓
      (LB.pull (LB.LinComb C.P.L.L (fun _ : Fin 1 => β) (fun _ => (Sc.k : ℤ))) (p' ≫ β')).U (fun _ => fun _ => c),
      ⟨m₁, m₂⟩, _, inf_le_left, _, inf_le_right, 1, fun j => ?_⟩
    rw [_root_.one_mul]
    refine fn_ext fun z hz => ?_
    have hz' : (p' ≫ β' ≫ β) z ∈ C.P.L.L.U c := by
      have := Set.mem_iInter.1 (mem_pull.1 hz.1) 0
      simpa using this
    obtain ⟨J, hJ, eJ⟩ := exists_good C.P.L.L hL z (fun _ : PUnit => p' ≫ β' ≫ β) (fun _ => c)
      (fun _ _ _ => rfl) (fun _ => hz')
    rw [gs_res _ _ _ hz, gs_res _ _ _ hz]
    refine (GlobalTheory.gs_chartSec (GlobalTheory.chartPullPull _ _) (σ j) (𝟙 _) z _ hz.2).trans
      (Eq.trans ?_ (GlobalTheory.gs_chartSec (GlobalTheory.chartPullPull _ _) (σ'' j) (𝟙 _) z _ hz.1).symm)
    rw [Category.id_comp, Category.id_comp]
    exact (sval_of (σ j) (p' ≫ β') z J (fun _ => c) (fun _ => by rw [Category.assoc]; exact eJ ⟨⟩)).symm.trans
      ((hv j _ _ _ _ hJ).symm.trans (sval_of (σ'' j) p' z J (fun _ => c) (fun _ => eJ ⟨⟩)))
  · have h₁ := hnz x hx
    choose J hJ using fun ψ : Sp Ω ⟶ C.G.left => exists_chart hL (ψ x)
    rw [GlobalTheory.TwistZero.mem_nonzeroLocus_iff _ _ _ hJ, hvθ _ _ _ _ hJ] at h₁
    refine DVR.nonzeroLocus_secOfIso w θ₁ hw C'.P.L.isLB (LB.isLB_pull hL β) ?_
    rw [GlobalTheory.TwistZero.mem_nonzeroLocus_iff _ _ _ hJ, hθ₁ _ _ _ _ hJ]
    exact h₁

end GlobalTheory.Mum.SecEmb
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedFibreThetaEmbeddingOfSections

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.SecEmb.geometricallyIrreducible_of_smooth {X S : Scheme.{0}} (f : X ⟶ S) (hs : Smooth f)
    (hc : GeometricallyConnected f) : GeometricallyIrreducible f := by
  constructor
  intro K _ g Z fst snd h
  have : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h hs
  have hcs := hc.geometrically_connectedSpace g fst snd h
  exact GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace K Z snd this hcs

theorem GlobalTheory.Mum.SecEmb.emb_of_traitRed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (G : Over M.S) [GrpObj G],
    IsSemiAbelian G → ∀ (B L : LB G.left), B.IsLB → L.IsLB → ∀ (N : ℕ) (s : Fin (N + 1) → B.Sec) (θ : L.Sec)
    (Y : Over (Sp (ResidueField R))) [GrpObj Y], Smooth Y.hom → ∀ (j : Y.left ⟶ PSpace R N),
    j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R) → IsImmersion j → ∀ (O : Y.left.Opens), (O : Set Y.left).Nonempty →
    GlobalTheory.Mum.SecEmb.TraitRed M G s θ Y j O → ∃ E : Emb M.π G, E.Theta L := by
  intro R _ _ _ hR M G _ hG B L hB hL N s θ Y _ hY j hj hi O hO hT
  have hH := GlobalTheory.Mum.SecEmb.mem_embH_of_closed R hR M G hG B L hB hL N s θ Y hY j hj hi O hT
  exact ⟨{ N := N
           H := GlobalTheory.Mum.SecEmb.embH s
           H_all := hH
           f := GlobalTheory.Mum.SecEmb.embF (G.hom ≫ M.π) s
           f_over := GlobalTheory.ProjSpace.toProj_str _ _ _
           Y := Y
           smooth := hY
           j := j
           j_over := hj
           imm := hi
           fib := fun Ω _ x κ hx => GlobalTheory.Mum.SecEmb.Fib.fib R hR M G hG B L hB hL N s θ Y hY j hj hi O hT hH Ω x κ hx },
    θ, O, hO, fun g y hy hc hf => GlobalTheory.Mum.SecEmb.ThetaPt.mem_basicOpen_theta R hR M G hG B L hB hL N s θ Y hY j hj hi O hT g y hy hc hf⟩

namespace GlobalTheory.Mum.SecEmb

theorem agree_pull {X P Q : Scheme.{0}} (L : LB X) {hP : P ⟶ X} {hQ : Q ⟶ X} (g : Q ⟶ P) (e : g ≫ hP = hQ) {k : ℕ}
    (σ : SecK L hP k) : ∃ σ' : SecK L hQ k, ∀ {Y : Scheme.{0}} {h : Y ⟶ X} (s : SecK L h k), Agree L σ s → Agree L σ' s := by
  subst e
  refine ⟨ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec σ g, fun s hs Z p p' hp z J hJ => ?_⟩
  rw [ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec σ g p z hJ]
  exact hs Z (p ≫ g) p' (by rw [Category.assoc]; exact hp) z J hJ

theorem traitReg_of_secs {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G : Over M.S) [GrpObj G]
    (L : LB G.left) {A : Scheme.{0}} (α : A ⟶ G.left) (Sc : Secs M G L α) :
    (∀ i, TraitReg M G L (Sc.s i)) ∧ TraitReg M G L Sc.θ := by
  constructor
  · intro i W _ _ _ hW φ ξ hinj hloc hξ
    obtain ⟨W', i1, i2, i3, io, G', iG', β, σ, θ', κ, e, hW', hio, hfin, hpb, -, -, hσ, -, -⟩ :=
      Sc.trait W hW φ ξ hinj hloc hξ
    obtain ⟨σ'', h''⟩ := agree_pull L hpb.1.isoPullback.inv hpb.1.isoPullback_inv_fst (σ i)
    exact ⟨W', i1, i2, i3, io, σ'', hW', hio, hfin, h'' _ (hσ i)⟩
  · intro W _ _ _ hW φ ξ hinj hloc hξ
    obtain ⟨W', i1, i2, i3, io, G', iG', β, σ, θ', κ, e, hW', hio, hfin, hpb, -, -, -, hθ, -⟩ :=
      Sc.trait W hW φ ξ hinj hloc hξ
    obtain ⟨σ'', h''⟩ := agree_pull L hpb.1.isoPullback.inv hpb.1.isoPullback_inv_fst θ'
    exact ⟨W', i1, i2, i3, io, σ'', hW', hio, hfin, h'' _ hθ⟩

theorem core : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C C' : LabCover D) (Sc : Secs C.toModif C.G C.P.L.L C.α) (h : C'.S ⟶ C.S) (β : C'.G.left ⟶ C.G.left),
    h ≫ C.π = C'.π → IsGrpPullback C'.G C.G h β → LBIso C'.P.L.L (C.P.L.L.pull β) →
    (∀ i, ∃ σ : SecK C.P.L.L β Sc.k, Agree C.P.L.L σ (Sc.s i)) → (∃ θ : SecK C.P.L.L β 1, Agree C.P.L.L θ Sc.θ) →
    ∃ E : Emb C'.π C'.G, E.Theta C'.P.L.L := by
  intro R _ _ _ hR D C C' Sc h β hπ hpb hL hs hθ
  choose σ hσ using hs
  obtain ⟨θ₀, hθ₀⟩ := hθ
  obtain ⟨θ, hT⟩ := GlobalTheory.Mum.SecEmb.traitRed_cover R hR D C C' Sc h β hπ hpb hL σ hσ θ₀ hθ₀
  exact GlobalTheory.Mum.SecEmb.emb_of_traitRed R hR C'.toModif C'.G C'.semi _ C'.P.L.L (LB.isLB_linComb C.P.L.isLB _ _) C'.P.L.isLB Sc.N σ θ Sc.Y Sc.smooth
    Sc.j Sc.j_over Sc.imm Sc.O Sc.O_ne hT

theorem emb_of_secs : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D), Nonempty (Secs C.toModif C.G C.P.L.L C.α) → ∃ (C' : LabCover D) (E : Emb C'.π C'.G), E.Theta C'.P.L.L := by
  intro R _ _ _ hR D C ⟨Sc⟩
  have hR' := hR
  obtain ⟨⟨hN, -, -, -⟩, hc⟩ := hR'
  have hsemi := C.semi
  obtain ⟨hs, hθ⟩ := traitReg_of_secs C.toModif C.G C.P.L.L C.α Sc
  obtain ⟨M', h, -, hgp, hπ, hσ⟩ := GlobalTheory.Mum.extend_finiteModif R C.toModif C.G hsemi.smooth hsemi.quasiCompact
    (GlobalTheory.Mum.SecEmb.geometricallyIrreducible_of_smooth _ hsemi.smooth hsemi.geomConnected) C.P.L.L C.P.L.isLB C.A.A.left C.α C.A.A.hom C.α_cart.1
    (Option (Fin (Sc.N + 1))) (fun o => o.elim 1 (fun _ => Sc.k))
    (Option.rec (motive := fun o => SecK C.P.L.L C.α (o.elim 1 (fun _ => Sc.k))) Sc.θ Sc.s)
    (by rintro (_ | i); exacts [hθ, hs i])
  obtain ⟨C', eS, β, hπ', hpb, hL⟩ := GlobalTheory.Mum.LabCover.exists_pull R D C M' h hgp hπ
  have hw : β ≫ C.G.hom = (C'.G.hom ≫ eS.hom) ≫ h := by rw [Category.assoc]; exact hpb.1.w
  refine ⟨C', core R hR D C C' Sc (eS.hom ≫ h) β (by rw [Category.assoc, hπ, hπ']) hpb hL ?_ ?_⟩
  · intro i
    obtain ⟨σ, hσi⟩ := hσ (some i)
    obtain ⟨σ', h'⟩ := agree_pull C.P.L.L (pullback.lift β (C'.G.hom ≫ eS.hom) hw) (pullback.lift_fst _ _ _) σ
    exact ⟨σ', h' _ hσi⟩
  · obtain ⟨σ, hσi⟩ := hσ none
    obtain ⟨σ', h'⟩ := agree_pull C.P.L.L (pullback.lift β (C'.G.hom ≫ eS.hom) hw) (pullback.lift_fst _ _ _) σ
    exact ⟨σ', h' _ hσi⟩

end GlobalTheory.Mum.SecEmb
end
end
