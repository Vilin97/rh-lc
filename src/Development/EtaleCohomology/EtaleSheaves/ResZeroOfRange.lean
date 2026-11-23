module

public import Development.EtaleCohomology.EtaleSheaves.CovOfPoints
public import Development.EtaleCohomology.EtaleSheaves.LeafTwSecKillCut
public import Development.EtaleCohomology.EtaleSheaves.LeafConeExactPf
public import Development.EtaleCohomology.EtaleSheaves.LeafNegPf
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
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
public import Mathlib.RingTheory.Etale.StandardEtale
public import Development.EtaleCohomology.EtaleSheaves.LeafTwFieldZPf
public import Development.EtaleCohomology.EtaleSheaves.LeafTwGenPf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

-- Source module: Development.EtaleCohomology.EtaleSheaves.LeafOfRingsLocInjPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8.TwSec

theorem jointlySurj_prec (P : MorphismProperty Scheme.{0}) : Scheme.JointlySurjective (Scheme.precoverage P) :=
  inferInstance

theorem LeafOfRingsLocInj_of : LeafOfRingsLocInj := by
  intro R _ M U t ht u
  have h0 : (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op U) t =
      (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op U) 0 := by
    have : ofRings.sec M U t = 0 := ht
    simp only [ofRings.sec] at this
    rw [map_zero]
    exact this
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) t 0 h0
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  have := jointlySurj_prec @Etale
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq u
  refine ⟨𝒰.X i, 𝒰.f i, 𝒰.map_prop i, ⟨y, hy⟩, ?_⟩
  have hm := hle _ _ (Presieve.ofArrows.mk i)
  have hm' : ((Scheme.Γ ⋙ M).map (𝒰.f i).op).hom t = ((Scheme.Γ ⋙ M).map (𝒰.f i).op).hom 0 := hm
  rw [map_zero] at hm'
  exact hm'

end LateralTheory.E.E8.TwSec
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.LeafOfRingsLocSurjPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafOfRingsLocSurjPf

theorem cover_hit {X : Scheme.{0}} (S : Sieve X) (hS : S ∈ Scheme.etaleTopology X) (x : X) :
    ∃ (U : Scheme.{0}) (w : U ⟶ X), Etale w ∧ x ∈ Set.range w ∧ S.arrows w := by
  obtain ⟨𝒰, h𝒰⟩ := (Scheme.mem_grothendieckTopology_iff).1 hS
  obtain ⟨i, hi⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 x
  exact ⟨𝒰.X i, 𝒰.f i, 𝒰.map_prop i, hi, h𝒰 _ _ (Presieve.ofArrows.mk i)⟩

theorem LeafOfRingsLocSurj_of : LateralTheory.E.E8.TwSec.LeafOfRingsLocSurj := by
  intro R _ M X s x
  have hS := Presheaf.imageSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (U := op X) s
  obtain ⟨U, w, hw, hx, t, ht⟩ := cover_hit _ hS x
  exact ⟨U, w, hw, hx, t, ht.symm⟩

end LateralTheory.E.LeafOfRingsLocSurjPf
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.LeafTwAdjPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.E.E8.TwSec

theorem twAdj_comap_surj (A : Type) [CommRing A] (q : ℕ) [NeZero q] :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A (AdjoinRoot (cyclotomic q A)))) := by
  have hm := cyclotomic.monic q A
  have := Module.Free.of_basis (AdjoinRoot.powerBasis' hm).basis
  have : Module.Finite A (AdjoinRoot (cyclotomic q A)) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis' hm).basis
  intro p
  have : Nontrivial A := by
    rcases subsingleton_or_nontrivial A with h | h
    · exact absurd (Subsingleton.elim p.asIdeal ⊤) p.isPrime.ne_top
    · exact h
  have : Nontrivial (AdjoinRoot (cyclotomic q A)) := by
    have hd : 0 < (cyclotomic q A).natDegree := by
      rw [natDegree_cyclotomic]; exact Nat.totient_pos.2 (NeZero.pos q)
    have : Nonempty (Fin (cyclotomic q A).natDegree) := ⟨⟨0, hd⟩⟩
    exact (AdjoinRoot.powerBasisAux' hm).repr.symm.injective.nontrivial
  exact Algebra.IsIntegral.comap_surjective A _ p

theorem twAdj_etale (A : Type) [CommRing A] (q : ℕ) (hq : IsUnit (q : A)) :
    Algebra.Etale A (AdjoinRoot (cyclotomic q A)) := by
  have hsep : (cyclotomic q A).Separable :=
    (separable_X_pow_sub_C_unit (1 : Aˣ) hq).of_dvd (by simpa using cyclotomic.dvd_X_pow_sub_one q A)
  obtain ⟨a, b, hab⟩ := hsep
  let P : StandardEtalePair A := ⟨cyclotomic q A, cyclotomic.monic q A, 1,
    ⟨b, a, 0, by rw [pow_zero, ← hab]; ring⟩⟩
  let e1 : P.Ring ≃ₐ[A] Localization.Away (AdjoinRoot.mk (cyclotomic q A) 1) := P.equivAwayAdjoinRoot
  let e2 : AdjoinRoot (cyclotomic q A) ≃ₐ[AdjoinRoot (cyclotomic q A)]
      Localization.Away (AdjoinRoot.mk (cyclotomic q A) 1) :=
    IsLocalization.atUnit _ _ (AdjoinRoot.mk (cyclotomic q A) 1) (by rw [map_one]; exact isUnit_one)
  have := Algebra.IsStandardEtale.of_equiv (e1.trans (e2.symm.restrictScalars A))
  infer_instance

theorem LeafTwAdj_of : LeafTwAdj := by
  intro q _ U u hq
  obtain ⟨R, f, hf, ⟨x, rfl⟩, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (X := U) (x := u) (U := ⊤) (by simp)
  have hqR : IsUnit ((q : ℕ) : R) := by
    simpa using (hq.map f.appTop.hom).map (Scheme.ΓSpecIso R).hom.hom
  have := twAdj_etale R q hqR
  let φ : R ⟶ CommRingCat.of (AdjoinRoot (cyclotomic q R)) :=
    CommRingCat.ofHom (algebraMap R (AdjoinRoot (cyclotomic q R)))
  have hφ : Etale (Spec.map φ) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr this)
  refine ⟨Spec (.of (AdjoinRoot (cyclotomic q R))), Spec.map φ ≫ f, inferInstance, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := twAdj_comap_surj R q x
    refine ⟨y, ?_⟩
    subst hy
    rfl
  · let ψ := (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot (cyclotomic q R)))).inv.hom
    refine ⟨⟨ψ (AdjoinRoot.root _), ?_, ?_⟩⟩
    · simpa using (hqR.map (algebraMap R (AdjoinRoot (cyclotomic q R)))).map ψ
    · have h0 : aeval (AdjoinRoot.root (cyclotomic q R)) (cyclotomic q ℤ) = 0 := by
        rw [← aeval_map_algebraMap R, map_cyclotomic, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
      have := aeval_algHom_apply ψ.toIntAlgHom (AdjoinRoot.root (cyclotomic q R)) (cyclotomic q ℤ)
      rw [h0, map_zero] at this
      exact this

end LateralTheory.E.E8.TwSec
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.LeafTwPtPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8.TwSec

theorem twF_res_comp {q : ℕ} (j : ℤ) {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (x : (twF q j).obj Γ(Z, ⊤)) :
    ((twF q j).map (Scheme.Γ.map (a ≫ b).op)).hom x =
      ((twF q j).map (Scheme.Γ.map a.op)).hom (((twF q j).map (Scheme.Γ.map b.op)).hom x) := by
  rw [op_comp, Functor.map_comp, Functor.map_comp]; rfl

theorem twF_map_cls {q : ℕ} (j : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (ζ : Prim q A) (c : ZMod q) :
    ((twF q j).map f).hom (ULift.up c • twCls j ζ) = ULift.up c • twCls j (ζ.map f.hom) := by
  rw [map_smul]
  congr 1
  unfold twCls
  change Submodule.mapQ _ _ _ (twRel_le q j f.hom) _ = _
  rw [Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem twF_eq_zero_of_not_unit {q : ℕ} (j : ℤ) {A : CommRingCat.{0}} (hq : ¬ IsUnit (q : A)) (t : (twF q j).obj A) :
    t = 0 := by
  haveI : IsEmpty (Prim q A) := ⟨fun ζ => hq ζ.2.1⟩
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  rw [Subsingleton.elim f 0]
  exact Submodule.Quotient.mk_zero _

theorem LeafTwPt_of (hA : LeafTwAdj) (hG : LeafTwGen) (hF : LeafTwFieldZ) : LeafTwPt := by
  intro q _ j U u t V g v hgv ht
  by_cases hq : IsUnit (q : Γ(U, ⊤))
  swap
  · refine ⟨U, 𝟙 U, inferInstance, ⟨u, rfl⟩, ?_⟩
    rw [twF_eq_zero_of_not_unit j hq t]; exact map_zero _
  obtain ⟨W₁, w₁, hw₁, ⟨w, hw⟩, ⟨ζ⟩⟩ := hA q U u hq
  haveI := hw₁
  obtain ⟨O, c, hwO, hO⟩ := hG q j W₁ ζ (((twF q j).map (Scheme.Γ.map w₁.op)).hom t) w
  have hO' : ((twF q j).map (Scheme.Γ.map (O.ι ≫ w₁).op)).hom t =
      ULift.up c • twCls j (ζ.map (Scheme.Γ.map O.ι.op).hom) := by
    rw [twF_res_comp, hO]; exact twF_map_cls j _ ζ c
  obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := O.ι ≫ w₁) (g := g)
    (⟨w, hwO⟩ : O.toScheme) v (by rw [hgv]; exact hw)
  have hc : c = 0 := by
    let P := pullback (O.ι ≫ w₁) g
    let φ := P.evaluation ⊤ p trivial
    have e : ((twF q j).map (Scheme.Γ.map (pullback.fst (O.ι ≫ w₁) g ≫ O.ι ≫ w₁).op)).hom t = 0 := by
      rw [pullback.condition, twF_res_comp, ht, map_zero]
    rw [twF_res_comp, hO', twF_map_cls] at e
    have key := twF_map_cls j φ (Prim.map (Scheme.Γ.map (pullback.fst (O.ι ≫ w₁) g).op).hom
      (Prim.map (Scheme.Γ.map O.ι.op).hom ζ)) c
    exact hF q j (P.residueField p) (Field.toIsField _) _ c
      (key.symm.trans ((congrArg (fun x => ((twF q j).map φ).hom x) e).trans (map_zero _)))
  refine ⟨O, O.ι ≫ w₁, inferInstance, ⟨⟨w, hwO⟩, hw⟩, ?_⟩
  rw [hO', hc]
  exact zero_smul (ULift (ZMod q)) _

end LateralTheory.E.E8.TwSec
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.PointDetect0Of

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.PointDetect0Pf

def EtSep : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) (s : Sec F X),
  (∀ x : X, ∃ (U : Scheme.{0}) (g : U ⟶ X), Etale g ∧ x ∈ Set.range g.base ∧ Sec.res g s = 0) → s = 0

theorem etSep : EtSep := by
  intro R _ F X s h
  choose U g hE hx h0 using h
  have hR : Presieve.ofArrows U g ∈ Scheme.precoverage @Etale X := by
    exact (Scheme.ofArrows_mem_precoverage_iff @Etale).2 ⟨fun x => ⟨x, hx x⟩, hE⟩
  have hT : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) := by
    have := (Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology F.obj (forget _)).1 F.property
    exact (isSheaf_iff_isSheaf_of_type _ _).1 this
  apply (hT.isSheafFor_of_mem_precoverage hR).isSeparatedFor.ext
  rintro Y f ⟨x⟩
  change Sec.res (g x) s = (F.obj.map (g x).op).hom 0
  rw [h0 x, map_zero]

end LateralTheory.E.PointDetect0Pf
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.ResZeroOfRange

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafSurj0WPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.E8.TwSec

theorem neg_cochain (R : Type) [CommRing R] (E : Spc) (F : Shv R) (m : ℤ) (hm : m < 0)
    (z : Cochain ((chains R).obj E) (res R F) m) : z = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  rw [Cochain.zero_v]
  by_cases hq : q < 0
  · exact (LateralTheory.E.LeafNegPf.res_isZero R F q hq).eq_of_tgt _ _
  · exact (LateralTheory.E.LeafNegPf.chains_isZero R E p (by omega)).eq_of_src _ _

theorem fgt_zero (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (y : Hrel R f F 0)
    (h : fgt R f F 0 y = 0) : y = 0 := by
  obtain ⟨z, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.inr ((chains R).map f))) z (zero_add 0)) = 0 at h
  rw [CohomologyClass.mk_eq_zero_iff] at h
  obtain ⟨m, hm, β, hβ⟩ := h
  rw [neg_cochain R E F m (by omega) β, δ_zero] at hβ
  have hz : z = 0 := by
    apply Cocycle.ext
    rw [mappingCone.ext_cochain_from_iff _ (-1) 0 (by omega)]
    refine ⟨(neg_cochain R U F _ (by omega) _).trans (neg_cochain R U F _ (by omega) _).symm, ?_⟩
    rw [Cocycle.coe_zero, Cochain.comp_zero]
    exact hβ.symm
  rw [hz]
  rfl

theorem pull_fgt (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (n : ℤ) (y : Hrel R f F n) :
    pull R f F n (fgt R f F n y) = 0 := by
  obtain ⟨z, rfl⟩ := y.mk_surjective
  exact LateralTheory.E.LeafConeExactPf.pre_inr_eq_zero _ n z

theorem twPt : LeafTwPt := LeafTwPt_of LeafTwAdj_of LeafTwGen_of LeafTwFieldZ_of

theorem secKill (q : ℕ) [NeZero q] {X Z : Scheme.{0}} (ι : Z ⟶ X) (j : ℤ) (s : Sec (tw q j) X) (hs : Sec.res ι s = 0)
    (z : Z) : ∃ (W : Scheme.{0}) (w : W ⟶ X), Etale w ∧ ι z ∈ Set.range w ∧ Sec.res w s = 0 := by
  obtain ⟨U, w, hw, ⟨u, hu⟩, t, ht⟩ := LateralTheory.E.LeafOfRingsLocSurjPf.LeafOfRingsLocSurj_of (ZMod q) (twF q j) X s (ι z)
  obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := w) (g := ι) u z hu
  have e2 : Sec.res (F := tw q j) (pullback.fst w ι) (Sec.res w s) = 0 := by
    rw [← res_comp, pullback.condition, res_comp, hs]
    exact map_zero _
  have hP : ofRings.sec (twF q j) _ (((twF q j).map (Scheme.Γ.map (pullback.fst w ι).op)).hom t) = 0 := by
    rw [← sec_res, ← ht]
    exact e2
  obtain ⟨V, v, -, ⟨v0, hv0⟩, hV⟩ := LeafOfRingsLocInj_of (ZMod q) (twF q j) _ _ hP p
  obtain ⟨W, w', hw', ⟨a, ha⟩, hW⟩ := twPt q j U u t V (v ≫ pullback.fst w ι) v0 (by simp [hv0, hp1])
    ((twF_res_comp j _ _ t).trans hV)
  refine ⟨W, w' ≫ w, inferInstance, ⟨a, by simp [ha, hu]⟩, ?_⟩
  rw [res_comp]
  have e := sec_res (twF q j) w' t
  rw [hW] at e
  exact (congrArg (Sec.res w') ht).trans (e.trans (sec_zero _ _))

def zeroLocus {R : Type} [CommRing R] {F : Shv R} {X : Scheme.{0}} (s : Sec F X) : Set X :=
  {x | ∃ (W : Scheme.{0}) (w : W ⟶ X), Etale w ∧ x ∈ Set.range w ∧ Sec.res w s = 0}

theorem isOpen_zeroLocus {R : Type} [CommRing R] {F : Shv R} {X : Scheme.{0}} (s : Sec F X) : IsOpen (zeroLocus s) := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨W, w, hw, hx, h0⟩
  exact ⟨Set.range w, fun y hy => ⟨W, w, hw, hy, h0⟩, w.isOpenMap.isOpen_range, hx⟩

theorem res_zero_of_range {R : Type} [CommRing R] {F : Shv R} {X T : Scheme.{0}} (s : Sec F X) (g : T ⟶ X)
    (hg : ∀ t, g t ∈ zeroLocus s) : Sec.res g s = 0 := by
  apply LateralTheory.E.PointDetect0Pf.etSep R F T
  intro t
  obtain ⟨W, w, hw, ⟨u, hu⟩, h0⟩ := hg t
  obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := w) t u hu.symm
  refine ⟨_, pullback.fst g w, inferInstance, ⟨p, hp1⟩, ?_⟩
  rw [← res_comp, pullback.condition, res_comp, h0]
  exact map_zero _

theorem core (h9 : A9) (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (ι : W ⟶ B) (P : Y ⟶ B) [IsProper P]
    (U : B.Etale) (y : Hrel (ZMod q) (sch.map (prU P ι U)) (tw q i) 0) (x : U.left) (hx : U.hom x ∈ Set.range ι) :
    ∃ (U' : B.Etale) (a : U' ⟶ U), x ∈ Set.range a.left ∧
      ∀ (U'' : B.Etale) (b : U'' ⟶ U'), rY q i P ι (b ≫ a) 0 y = 0 := by
  obtain ⟨e, he, -⟩ := (h9 (ZMod q) (tw q i)).2
  obtain ⟨s, hs⟩ := (e (YU P U)).surjective (fgt (ZMod q) (sch.map (prU P ι U)) (tw q i) 0 y)
  have hZ : Sec.res (prU P ι U) s = 0 := by
    apply (e _).injective
    rw [← he, hs, map_zero]
    exact pull_fgt _ _ _ _ _
  have hcl : IsClosed ((toBY P U) '' (zeroLocus s)ᶜ) :=
    (toBY P U).isClosedMap _ (isOpen_zeroLocus s).isClosed_compl
  let O : U.left.Opens := ⟨_, hcl.isOpen_compl⟩
  have hxO : x ∈ O := by
    rintro ⟨t, ht, htx⟩
    obtain ⟨w0, hw0⟩ := hx
    obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd P U.hom ≫ U.hom) (g := ι) t w0
      (by rw [hw0, ← htx]; rfl)
    apply ht
    rw [← hp1]
    exact secKill q (prU P ι U) i s hZ p
  have hU : Etale U.hom := U.prop
  let U' : B.Etale := MorphismProperty.Over.mk ⊤ (O.ι ≫ U.hom) (inferInstanceAs (Etale (O.ι ≫ U.hom)))
  let a : U' ⟶ U := MorphismProperty.Over.homMk O.ι rfl
  refine ⟨U', a, ⟨⟨x, hxO⟩, rfl⟩, fun U'' b => ?_⟩
  apply fgt_zero
  refine (relNat _ _ _ _ _ _ _ _ _).trans ?_
  rw [← hs, he, res_zero_of_range s _ ?_, map_zero]
  intro t
  by_contra hn
  have h1 : resY P (b ≫ a) ≫ toBY P U = (toBY P U'' ≫ b.left) ≫ O.ι := by
    simp only [resY, toBY, pullback.lift_snd]
    rfl
  have h2 : toBY P U (resY P (b ≫ a) t) ∈ O := by
    rw [← Scheme.Hom.comp_apply, h1]
    exact ((toBY P U'' ≫ b.left) t).2
  exact h2 ⟨_, hn, rfl⟩

theorem LeafSurj0W_of : LateralTheory.E.LeafSurj0Pf.LeafSurj0W := by
  intro hy q _ k _ _ i B W Y0 Y1 Y2 _ ι _ V _ p g1 g2 _ _ h2 _ U y x hx
  exact core hy.2.2.2.2.2.2.2.1 q i ι (g2 ≫ g1 ≫ p) U y x hx

end LateralTheory.E.LeafSurj0WPf
end
end
end
