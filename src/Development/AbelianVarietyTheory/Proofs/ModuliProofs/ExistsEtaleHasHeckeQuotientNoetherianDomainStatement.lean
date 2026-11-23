module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenWeilIsIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfIsReduced
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEtaleLinearisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientTripleFamilyReducedNoetherianStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSubgroupEqRangeOfLists
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsHeckeIsog
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTateIsoHeckeQuotient
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueTangentLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfProper
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WeilRos
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeOfIsPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.WittVector.IsPoly
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjIsAbelianSchemeDimRigidifiedSym

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfSections

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

noncomputable section

namespace GlobalTheory

namespace SectionQuot

open PointQuot

variable {S : Scheme.{0}}

lemma exists_geomPt (Z : Over S) (z : Z.left) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (t : Sp k ⟶ S), Nonempty (Over.mk t ⟶ Z) := by
  let k := AlgebraicClosure (Z.left.residueField z)
  let p : Sp k ⟶ Z.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (Z.left.residueField z) k)) ≫
      Z.left.fromSpecResidueField z
  exact ⟨k, inferInstance, inferInstance, p ≫ Z.hom, ⟨Over.homMk p rfl⟩⟩

lemma mono_constDesc_of_geom {I : Type} {A : Over S} (x : I → (𝟙_ (Over S) ⟶ A))
    (hx : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (c d : I),
      toUnit (Over.mk t) ≫ x c = toUnit (Over.mk t) ≫ x d → c = d) : Mono (constDesc x) := by
  refine ⟨fun {Z} f g h => hom_ext_local f g fun z => ?_⟩
  obtain ⟨V, hV, c, hc⟩ := locally_const f z
  obtain ⟨W, hW, d, hd⟩ := locally_const g z
  have hc' := const_of_le (inf_le_left : V ⊓ W ≤ V) hc
  have hd' := const_of_le (inf_le_right : V ⊓ W ≤ W) hd
  obtain ⟨k, _, _, t, ⟨p⟩⟩ :=
    exists_geomPt (openObj Z (V ⊓ W)) (⟨z, hV, hW⟩ : (V ⊓ W : Z.left.Opens))
  obtain rfl : c = d := by
    apply hx k t
    rw [toUnit_unique (toUnit _) (p ≫ toUnit _), Category.assoc, Category.assoc,
      ← constPt_desc x c, ← constPt_desc x d, ← reassoc_of% hc', ← reassoc_of% hd', h]
  exact ⟨V ⊓ W, ⟨hV, hW⟩, hc'.trans hd'.symm⟩

end SectionQuot


open PointQuot SectionQuot in
theorem exists_quotient_by_finite_group_of_sections :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (C : Type) [CommGroup C] [Finite C] (i : C →* (𝟙_ (Over (Sp R)) ⟶ P.A)), (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (c : C), toUnit (Over.mk t) ≫ i c = 1 → c = 1) → ∃ (B : Over (Sp R)) (_ : GrpObj B) (ψ : P.A ⟶ B), IsAbelianScheme B ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ c, i c ≫ ψ = 1) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (x : Over.mk t ⟶ P.A), x ≫ ψ = 1 ↔ ∃ c, x = toUnit _ ≫ i c := by
  open SectionQuot PointQuot in
    intro R _ _ P C _ _ i hi
    have L : Out.Laws := GlobalTheory.firstFiveLaws.1
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin C
    let x : Fin n → (𝟙_ (Over (Sp R)) ⟶ P.A) := fun c => i (e.symm c)
    have hr : Set.range x = i.range := by
      ext y
      exact ⟨by rintro ⟨c, rfl⟩; exact ⟨e.symm c, rfl⟩,
        by rintro ⟨c, rfl⟩; exact ⟨e c, by simp [x]⟩⟩
    have hmono : Mono (constDesc x) := mono_constDesc_of_geom x fun k _ _ t c d h => by
      apply e.symm.injective
      rw [← div_eq_one]
      apply hi k t
      rw [map_div, GrpObj.comp_div, div_eq_one]
      exact h
    obtain ⟨_, hhom⟩ := exists_grpObj_constObj x i.range hr
    have hs : FinEt.IsSplitOfRank (constObj (Sp R) (Fin n)).hom n :=
      (FinEt.isSplitOfRank_iff_exists_iso _ _).mpr ⟨Iso.refl _, Category.id_comp _⟩
    have het := hs.etale
    obtain ⟨B, _, hB, q, hq, hfin, hflat, hsurj, hker⟩ :=
      L.quotient R P (constObj (Sp R) (Fin n)) (constDesc x) hhom hmono hs.isFinite inferInstance
    have hw : constDesc x ≫ q = 1 := hker.w
    have hkill : ∀ c, i c ≫ q = 1 := fun c => by
      have : i c = x (e c) := by simp [x]
      rw [this, ← constPt_desc x (e c), Category.assoc, hw, MonObj.comp_one]
    refine ⟨B, inferInstance, q, hB, hq, hfin, ?_, hsurj, hkill,
      fun k _ _ t y => ⟨fun hy => ?_, ?_⟩⟩
    · refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Etale)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
        ((H1.torsor_pullback (constDesc x) q hker).map (Over.forget _)).flip
        ⟨⟨hsurj, hflat⟩, inferInstanceAs (QuasiCompact q.left)⟩ ?_
      exact MorphismProperty.of_isPullback (P := @Etale) (IsPullback.of_hasPullback _ _) het
    · obtain ⟨z⟩ : Nonempty (Over.mk t).left := inferInstanceAs (Nonempty (PrimeSpectrum k))
      have : Subsingleton (Over.mk t).left := inferInstanceAs (Subsingleton (PrimeSpectrum k))
      obtain ⟨V, hV, c, hc⟩ := locally_const_desc x (hker.lift y (toUnit _) hy) z
      rw [hker.lift_fst] at hc
      refine ⟨e.symm c, hom_ext_local _ _ fun z' => ⟨V, Subsingleton.elim z z' ▸ hV, ?_⟩⟩
      rw [hc, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
    · rintro ⟨c, rfl⟩
      rw [Category.assoc, hkill, MonObj.comp_one]

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasQuotOfIsIsogT

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory

open HeckePoint

theorem hasQuot_of_isIsogT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o : Ob D l s) (t' : SAB H S) (ψ : o.t.G ⟶ t'.G) (K : Set o.t.G.left), 1 ≤ D.p + D.q → admitted l 𝔓 p → IsProper t'.G.hom → Out.RelAmple t'.G t'.PP.L → Out.KTriv t'.G t'.PP.L → IsIsogT o.t t' p ψ → KerSet ψ K → HeckeSet D o.t 𝔓 p i K → HasQuot o p K := by
  intro E _ _ _ H D l 𝔓 p i S _ s o t' ψ K _ ⟨h𝔓, hco, hp, hp𝔓, hpM⟩ hpr ham hkt hI hker hHk
  obtain ⟨hhom, hfin, het, hsur, hlin, hiso⟩ := hI
  have hG : Out.GlobalFnsSt := (show Out.Laws from GlobalTheory.firstFiveLaws.1).globalFns
  have hab := isAbelianScheme_of_proper o.t o.proper
  have hab' := isAbelianScheme_of_proper t' hpr
  have hW := fun (n : ℤ) (T : Over S) (x y : T ⟶ o.t.G) c c' =>
    weilIs_along_hom hG _ o.t.G t'.G ψ o.t.PP.L t'.PP.L (p ^ 2) n T x y c c' hab hab' o.t.PP.isLB t'.PP.isLB hhom hiso
  obtain ⟨p₀, hp₀⟩ := exists_inv_mod hp hpM
  have hMM : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hAM : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
  have etaM : ∀ a, o.eta (l.M • a) = 1 := fun a => o.eta_ker _ (by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul (natCast_M_mem l) Submodule.mem_top)
  let o' : Ob D l s :=
    { t := t', proper := hpr, ample := ham, ktriv := hkt
      eta := fun a => o.eta (p₀ • a) ≫ ψ
      eta_add := fun a c => by rw [smul_add, o.eta_add, MonObj.mul_comp]
      eta_ker := fun a ha => by rw [o.eta_ker _ (nsmul_mem ha _), MonObj.one_comp]
      etaA := fun a => o.etaA (p₀ • a) ≫ ψ
      etaA_add := fun a c => by rw [smul_add, o.etaA_add, MonObj.mul_comp]
      etaA_ker := fun a => by rw [smul_comm, o.etaA_ker, MonObj.one_comp]
      geom := by
        intro k _ _ x β hx
        obtain ⟨hdet, I, hζ, hA, hM⟩ := o.geom k x β hx
        refine ⟨fun τ => ?_, ?_⟩
        · simp only [← LieEtale.lieMult_iff_of_etale _ _ _ _ ψ o.t.act t'.act hhom het hlin k x τ]
          exact hdet τ
        obtain ⟨C, hC, -, c₂, c₃, c₄, c₅, -⟩ := hHk k x
        have mem : ∀ z : Over.mk x ⟶ o.t.G, z ≫ ψ = 1 ↔ z ∈ C := fun z => (hker k x z).trans (hC z).symm
        let ψx : (Over.mk x ⟶ o.t.G) →* (Over.mk x ⟶ t'.G) :=
          MonoidHom.mk' (fun z => z ≫ ψ) fun a c => MonObj.mul_comp a c ψ
        have uniq : ∀ (n : ℤ) (z w : Over.mk x ⟶ o.t.G) (c c' : kˣ),
            Out.WeilIs o.t.G o.t.PP.L n z w (unitOn c) → Out.WeilIs o.t.G o.t.PP.L n z w (unitOn c') → c = c' :=
          fun n z w c c' h h' => (unitOn_bijective k).1 (CommutatorPairing.weilIs_unique hG hab o.t.PP.isLB h h')
        obtain ⟨I', hζ', hev⟩ := exists_tateIso_heckeQuotient SimAlg.sim_group E H D 𝔓 p k _ _ _
          (fun a g => g ≫ t'.act.act a) _
          (fun n g g' c => Out.WeilIs t'.G t'.PP.L n g g' (unitOn c)) I ψx h𝔓 hco hp hp𝔓
          (fun y => exists_lift_pt ψ x y)
          (fun a z => by
            show (z ≫ _) ≫ ψ = (z ≫ ψ) ≫ _
            rw [Category.assoc, hlin, Category.assoc])
          (fun J hJ z _ hz' => (mem z).2 (c₂ J hJ hz'))
          (fun z hz => ⟨by
            rw [← comp_act_natCast o.t.act]
            refine c₃ ((mem z).1 hz) _ ?_
            rw [Nat.cast_pow, pow_two]
            refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
            have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hp𝔓
            rwa [map_natCast] at this, c₃ ((mem z).1 hz)⟩)
          (fun z w hz hw => by
            have h := c₄ z ((mem z).1 hz) w ((mem w).1 hw)
            rw [← Nat.cast_pow] at h
            exact (congrArg (Out.WeilIs o.t.G o.t.PP.L ((p ^ 2 : ℕ) : ℤ) z w) unitOn_one).mpr h)
          (by rw [← c₅, show ψx.ker = C from Subgroup.ext mem])
          (fun n z w c c' _ _ _ h h' => uniq n z w c c' h h')
          (fun n z w c hn hz hw h => by
            have hlift : ∀ (q : Over.mk x ⟶ t'.G), q ^ n = 1 →
                ∀ a : (Over.mk x).left, ∃ V : (Over.mk x).left.Opens, a ∈ V ∧
                  ∃ θ : Out.ThetaGrp t'.G t'.PP.L n (Out.overRes V), θ.pt = Out.overResι V ≫ q := by
              intro q hq a
              obtain ⟨V, hV, v, hv⟩ := exists_local_gen t'.PP.isLB (K := Fin 2)
                ![(1 : Over.mk x ⟶ t'.G).left, q.left] ![(n : ℤ), -(n : ℤ)] a
              refine ⟨V, hV, ?_⟩
              apply exists_theta t'.cub (by rw [← MonObj.comp_pow, hq, MonObj.comp_one]) v hv
              intro U _ f
              rw [Fin.prod_univ_two, ← MonObj.comp_one (Out.overResι V)]
              rfl
            obtain ⟨c', hc'⟩ := CommutatorPairing.exists_weilIs hG hab' t'.PP.isLB (hlift _ hz) (hlift _ hw)
            obtain ⟨c', rfl⟩ := (unitOn_bijective k).2 c'
            have h₂ := (hW n _ z w 1 _ hc').1
            rw [← Nat.cast_mul] at h₂
            rw [uniq _ z w c c' h h₂]
            exact hc')
        refine ⟨I', by rw [hζ']; exact hζ, fun a => ?_, fun a ha => ?_⟩
        · rw [hev l.A p₀ l.A_pos (hp₀.of_dvd hAM), ← hA, ← Category.assoc]; rfl
        · rw [hev l.M p₀ (by have := l.three_le; omega) (hp₀.of_dvd hMM), ← hM _ (nsmul_mem ha _),
            ← Category.assoc]; rfl }
  refine ⟨o', ψ, ⟨⟨hhom, hfin, het, hsur, hlin, hiso⟩, fun p' hp' a => ?_⟩, hker⟩
  have e := modEq_of_inv hp' hp₀
  exact ⟨congrArg (· ≫ ψ) (eq_of_modEq o.eta o.eta_add etaM (e.of_dvd hMM) a),
    congrArg (· ≫ ψ) (eq_of_modEq o.etaA o.etaA_add o.etaA_ker (e.of_dvd hAM) a)⟩

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEtaleHasHeckeQuotientNoetherianDomain

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkLoc

theorem range_subset_iff {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsSeparated G.hom] {N n : ℕ}
    {σ : Fin n → (𝟙_ (Over S) ⟶ G)} {K : Set G.left} (h : Lists N σ K) {k : Type} [Field k] (x : Sp k ⟶ S)
    (z : Over.mk x ⟶ G) : Set.range z.left ⊆ K ↔ ∃ j, z = toUnit _ ≫ σ j := by
  obtain ⟨-, rfl, -⟩ := h
  obtain ⟨q⟩ : Nonempty (Sp k) := inferInstance
  constructor
  · intro hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hz ⟨q, rfl⟩)
    have h1 := ListedSubgroup.eq_comp_section G.hom (σ j).left (Over.w (σ j)) _ q hj
    rw [Over.w z] at h1
    exact ⟨j, Over.OverMorphism.ext h1⟩
  · rintro ⟨j, rfl⟩ _ ⟨y, rfl⟩
    exact Set.mem_iUnion.2 ⟨j, x y, (Scheme.Hom.comp_apply x (σ j).left y).symm⟩

theorem isUnit_natCast {F R : Type} [Field F] [CharZero F] [CommRing R] (s : Sp R ⟶ Sp F) (m : ℕ) (hm : 0 < m) :
    IsUnit (m : R) := by
  have h : IsUnit (m : F) := (Nat.cast_ne_zero.2 hm.ne').isUnit
  simpa using h.map (Spec.preimage s).hom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

noncomputable abbrev pol {S : Scheme.{0}} {s : S ⟶ Sp (KA l)} (o : Ob D l s) : Out.PolAV S :=
  have h := GlobalTheory.obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ S s o
  { A := o.t.G, isAb := h.1, g := Module.finrank ℚ E / 2 * (D.p + D.q), smoothDim := h.2.1, L := o.t.PP.L,
    isLB := o.t.PP.isLB, rigid := h.2.2.1, sym := h.2.2.2, ample := o.ample, ktriv := o.ktriv }

theorem weilIs_one {S : Scheme.{0}} [ConnectedSpace S] {s : S ⟶ Sp (KA l)} (o : Ob D l s) {𝔓 : Ideal (𝓞 E)}
    {p i n : ℕ} {σ : Fin n → (𝟙_ (Over S) ⟶ o.t.G)} {K : Set o.t.G.left} (hp : 0 < p)
    (hu : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤))) (hL : Lists (p ^ 2) σ K) (hH : HeckeSet D o.t 𝔓 p i K) (j j' : Fin n) :
    Out.WeilIs o.t.G o.t.PP.L ((p ^ 2 : ℕ) : ℤ) (σ j) (σ j') 1 := by
  have := o.proper
  obtain ⟨U, hU, hW⟩ := GlobalTheory.exists_clopen_weilIs_iff GlobalTheory.firstFiveLaws.1 S (pol o) (p ^ 2) (𝟙_ (Over S)) (σ j) (σ j') 1
    (pow_pos hp 2) hu (hL.1 j) (hL.1 j') (one_pow _)
  obtain ⟨s₀⟩ : Nonempty S := inferInstance
  let k : Type := AlgebraicClosure (S.residueField s₀)
  let x : Sp k ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s₀) k)) ≫ S.fromSpecResidueField s₀
  obtain ⟨C, hC, hk⟩ := hH k x
  obtain ⟨q⟩ : Nonempty (Sp k) := inferInstance
  have hmem : ∀ j, toUnit (Over.mk x) ≫ σ j ∈ C := fun j =>
    (hC _).2 ((range_subset_iff hL x _).2 ⟨j, rfl⟩)
  have h₁ := (hW (Over.mk x) (toUnit _)).1 (by
    rw [map_one, Nat.cast_pow]
    exact hk.2.2.2.1 _ (hmem j) _ (hmem j'))
  have : ConnectedSpace (𝟙_ (Over S)).left := ‹ConnectedSpace S›
  have hc : IsClopen (U : Set (𝟙_ (Over S)).left) := ⟨hU, U.isOpen⟩
  have h₂ : (U : Set (𝟙_ (Over S)).left) = Set.univ := hc.eq_univ ⟨_, h₁ ⟨q, rfl⟩⟩
  have h₃ := (hW (𝟙_ (Over S)) (𝟙 _)).2 (by rw [h₂]; exact Set.subset_univ _)
  rw [map_one, Category.id_comp, Category.id_comp] at h₃
  exact h₃

theorem hasQuot_of_linearisation {R : Type} [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R]
    {s : Sp R ⟶ Sp (KA l)} (o : Ob D l s) {𝔓 : Ideal (𝓞 E)} {p i n : ℕ}
    {σ : Fin n → (𝟙_ (Over (Sp R)) ⟶ o.t.G)} {K : Set o.t.G.left} (hD : 1 ≤ D.p + D.q) (hA : admitted l 𝔓 p)
    (hL : Lists (p ^ 2) σ K) (hH : HeckeSet D o.t 𝔓 p i K) (C : Type) [CommGroup C] [Finite C]
    (v : C →* (𝟙_ (Over (Sp R)) ⟶ o.t.G)) (e : C → Fin n) (he : Function.Injective e) (hv : ∀ c, v c = σ (e c))
    (hσ : ∀ j, ∃ c, v c = σ j)
    (hu : ∃ u : ∀ c : C, LB.Gen (LB.LinComb (lbPow o.t.PP.L (p ^ 2)) (K := Fin 2)
        ![𝟙 o.t.G.left, ((toUnit o.t.G ≫ v c) * 𝟙 o.t.G).left] ![1, -1]), (∀ c, (u c).IsGen) ∧
      ∀ c c', LB.Gen.Corr (lbPow o.t.PP.L (p ^ 2)) _ _ _ _ (u (c * c')) (LB.mulGen (lbPow o.t.PP.L (p ^ 2)) _ _ _ _ (u c)
        (LB.pullGen (lbPow o.t.PP.L (p ^ 2)) _ _ (u c') ((toUnit o.t.G ≫ v c) * 𝟙 o.t.G).left))) :
    HasQuot o p K := by
  have := o.proper
  obtain ⟨u, hu₁, hu₂⟩ := hu
  have hinj : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (c : C),
      toUnit (Over.mk t) ≫ v c = 1 → c = 1 := fun k _ _ t c h => by
    have h₁ : toUnit (Over.mk t) ≫ v c = toUnit (Over.mk t) ≫ v 1 := by rw [h, map_one, MonObj.comp_one]
    rw [hv, hv] at h₁
    exact he (hL.2.2 k t (congrArg CommaMorphism.left h₁))
  obtain ⟨B, gB, ψ, hB, hψ, hf, het, hs, hk₁, hk₂⟩ : ∃ (B : Over (Sp R)) (_ : GrpObj B) (ψ : o.t.G ⟶ B),
      IsAbelianScheme B ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ c, v c ≫ ψ = 1) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (x : Over.mk t ⟶ o.t.G),
        x ≫ ψ = 1 ↔ ∃ c, x = toUnit _ ≫ v c :=
    GlobalTheory.exists_quotient_by_finite_group_of_sections R (pol o) C v hinj
  obtain ⟨M, hM, hiso⟩ := GlobalTheory.LinDescent.exists_descent (Sp R) o.t.G B ψ C v (lbPow o.t.PP.L (p ^ 2))
    (LB.isLB_linComb o.t.PP.isLB _ _) hψ hf het hs hk₁ (fun k _ _ t => ⟨hk₂ k t, hinj k t⟩) u hu₁ hu₂
  have hker : KerSet ψ K := fun k _ _ t z => by
    rw [hk₂, range_subset_iff hL]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨e c, by rw [hv]⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨c, hc⟩ := hσ j
      exact ⟨c, by rw [hc]⟩
  obtain ⟨t', ψ', h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.T.exists_quotient_triple_family_reduced_noetherian E H R o.t _ p B ψ M (isUnit_natCast s) hA.2.2.1.pos o.proper
    (pol o).smoothDim o.ample o.ktriv hB hM hψ hf het hs (fun k _ _ x => by
      obtain ⟨C₀, hC₀, hk⟩ := hH k x
      have hm : ∀ z : Over.mk x ⟶ o.t.G, z ≫ ψ = 1 ↔ z ∈ C₀ := fun z => (hker k x z).trans (hC₀ z).symm
      refine ⟨(Nat.card_congr (Equiv.subtypeEquivRight hm)).trans hk.2.2.2.2.1, fun z hz => ⟨?_, fun a => ?_⟩⟩
      · obtain ⟨c, rfl⟩ := (hk₂ k x z).1 hz
        rw [← MonObj.comp_pow, hv, hL.1, MonObj.comp_one]
      · exact (hm _).2 (hk.1 z ((hm z).1 hz) a)) hiso
  exact GlobalTheory.hasQuot_of_isIsogT E H D l 𝔓 p i (Sp R) s o t' ψ' K hD hA h₁ h₂ h₃ h₄
    (fun k _ _ x z => (h₅ _ z).trans (hker k x z)) hH

end GlobalTheory.HkLoc


open GlobalTheory.HkLoc in
theorem GlobalTheory.exists_etale_hasQuot_of_lists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] (s : Sp R ⟶ Sp (KA l)) (o : Ob D l s) (σ : Fin n → (𝟙_ (Over (Sp R)) ⟶ o.t.G)) (K : Set o.t.G.left) (q : Sp R), 1 ≤ D.p + D.q → admitted l 𝔓 p → Lists (p ^ 2) σ K → HeckeSet D o.t 𝔓 p i K → ∃ (R' : Type) (_ : CommRing R') (π : Sp R' ⟶ Sp R) (o' : Ob D l (π ≫ s)) (m : ObjMap o' o π), Etale π ∧ q ∈ Set.range π ∧ HasQuot o' p (m.toSABMap.φ ⁻¹' K) := by
  intro E _ _ _ H D l 𝔓 p i n R _ _ _ s o σ K q hD hA hL hH
  have hp : 0 < p := hA.2.2.1.pos
  have hΓ : ∀ m : ℕ, 0 < m → IsUnit (m : Γ(Sp R, ⊤)) := fun m hm => by
    simpa using (isUnit_natCast s m hm).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  obtain ⟨C, hC⟩ := GlobalTheory.HkFam.exists_subgroup_eq_range_of_lists E H D 𝔓 p i n (Sp R) o.t σ K o.proper (hΓ p hp) hL hH
  have hmem : ∀ c : C, ∃ j, σ j = c := fun c => by
    have : c.1 ∈ (C : Set (𝟙_ (Over (Sp R)) ⟶ o.t.G)) := c.2
    rwa [hC] at this
  choose e he using hmem
  have einj : Function.Injective e := fun c c' h => Subtype.ext (by rw [← he, h, he])
  have : Finite C := Finite.of_injective e einj
  obtain ⟨R', _, _, het, hq, hlin⟩ := GlobalTheory.exists_etale_linearisation R (pol o) (p ^ 2) C C.subtype q
    (isUnit_natCast s _ (pow_pos hp 2)) (pow_pos hp 2)
    (fun c => Subtype.ext (by
      have := hL.1 (e c)
      rw [he] at this
      exact this))
    (fun c c' => by
      have := weilIs_one o hp (hΓ _ (pow_pos hp 2)) hL hH (e c) (e c')
      rw [he, he] at this
      exact this)
  let π : Sp R' ⟶ Sp R := spMap (algebraMap R R')
  have hπ : Etale π := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.2 het
  have : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  have : AlgebraicGeometry.IsReduced (Sp R') := GlobalTheory.isReduced_of_smooth_of_isReduced π
  have : _root_.IsReduced R' := (affine_isReduced_iff (CommRingCat.of R')).1 this
  obtain ⟨o', ⟨m⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ s (π ≫ s) π rfl rfl
    (by simp [spMap]) o
  obtain ⟨h₁, -, h₂⟩ := (GlobalTheory.heckeSets_pull E H D 𝔓 p i _ _ o.t o'.t π m.toSABMap o.proper).2 K
  obtain ⟨σ', hσ', hL'⟩ := h₂ _ _ σ hL
  obtain ⟨ρ, e₀⟩ := GlobalTheory.HkSetPull.exists_equiv m.cart (𝟙_ (Over (Sp R')))
  have tu : (toUnit (Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ π))).left = π := by simp
  let v : C →* (𝟙_ (Over (Sp R')) ⟶ o'.t.G) := MonoidHom.mk' (fun c => ρ.symm (toUnit _ ≫ c.1)) fun c c' => by
    rw [← map_mul, ← MonObj.comp_mul]
    rfl
  have hv : ∀ c, (v c).left ≫ m.toSABMap.φ = π ≫ c.1.left := fun c => by
    change (ρ.symm (toUnit _ ≫ c.1)).left ≫ _ = _
    rw [← e₀, ρ.apply_symm_apply, Over.comp_left, tu]
  have hv' : ∀ (c : C) j, σ j = c → v c = σ' j := fun c j h =>
    Over.OverMorphism.ext (m.cart.1.hom_ext (by rw [hv, hσ', h]) ((Over.w _).trans (Over.w _).symm))
  refine ⟨R', inferInstance, π, o', m, hπ, hq, hasQuot_of_linearisation o' hD hA hL' (h₁ hH) C v e einj
    (fun c => hv' c _ (he c)) (fun j => ⟨⟨σ j, ?_⟩, hv' _ j rfl⟩) ?_⟩
  · change σ j ∈ (C : Set (𝟙_ (Over (Sp R)) ⟶ o.t.G))
    rw [hC]
    exact ⟨j, rfl⟩
  · exact hlin o'.t.G m.toSABMap.φ o'.t.PP.L v m.cart o'.t.PP.isLB (m.lin.imp fun _ h => h.1) hv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEtaleHasHeckeQuotientNoetherianDomainStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

theorem _root_.GlobalTheory.T.exists_etale_hasHeckeQuotient_noetherian_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] (s : Sp R ⟶ Sp (KA l)) (o : Ob D l s) (σ : Fin n → (𝟙_ (Over (Sp R)) ⟶ o.t.G)) (K : Set o.t.G.left) (q : Sp R), 1 ≤ D.p + D.q → admitted l 𝔓 p → Lists (p ^ 2) σ K → HeckeSet D o.t 𝔓 p i K → ∃ (R' : Type) (_ : CommRing R') (π : Sp R' ⟶ Sp R) (o' : Ob D l (π ≫ s)) (m : ObjMap o' o π), Etale π ∧ q ∈ Set.range π ∧ HasQuot o' p (m.toSABMap.φ ⁻¹' K) := by
  first | exact @GlobalTheory.exists_etale_hasQuot_of_lists | exact GlobalTheory.exists_etale_hasQuot_of_lists | (intros; apply GlobalTheory.exists_etale_hasQuot_of_lists <;> assumption)
end
end
