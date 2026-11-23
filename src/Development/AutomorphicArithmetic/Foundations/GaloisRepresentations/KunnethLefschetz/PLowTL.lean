module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
public import Development.EtaleCohomology.EtaleTrace.TorsionH0PointOfLocalTwist
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
public import Development.EtaleCohomology.EtaleTrace.PrimSplitPf
public import Development.EtaleCohomology.EtaleTrace.EtaleTateTwistSectionConstantOnPointsOfConnected
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.EtaleCohomology.EtaleTrace.PtCoverPf
public import Development.EtaleCohomology.EtaleTrace.TateTwistSectionConstantOnPointsOfTwLocPtCov
public import Development.EtaleCohomology.EtaleTrace.TwZeroPf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Polynomial.Basic
public import Development.EtaleCohomology.TateTwists.AlgPowPfR
public import Development.EtaleCohomology.TateTwists.TwTorsPfR
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.TypeStar

-- Source module: Development.EtaleCohomology.EtaleTrace.CocEqPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CochainComplex.HomComplex Opposite

namespace LateralTheory.EtaleTrace

theorem free_ext (R : Type) [CommRing R] (P : PSh) {G : Shv R} (f g : (free R).obj P ⟶ G)
    (h : ∀ (U : Scheme.{0}) (x : P.obj (op U)),
      (f.hom.app (op U)).hom (freeGen R P U x) = (g.hom.app (op U)).hom (freeGen R P U x)) : f = g := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext (J := Scheme.etaleTopology) (P := (freeP R).obj P) f.hom g.hom G.property ?_
  ext U : 2
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  have := h U.unop x
  simp only [freeGen] at this
  simp only [freeP, ModuleCat.freeMk] at this
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
  exact this

theorem cocEq : CocEq := by
  intro R _ F X α β h
  apply Cocycle.ext
  apply Cochain.ext₀
  intro q
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · have : (res R F).IsStrictlyGE 0 := by unfold res; infer_instance
    exact (CochainComplex.isZero_of_isStrictlyGE (res R F) 0 q hq).eq_of_tgt _ _
  · have key : (chainsXIso R (sch.obj X) 0).inv ≫ α.1.v _ _ (show -((0:ℕ):ℤ) + 0 = 0 by simp) =
        (chainsXIso R (sch.obj X) 0).inv ≫ β.1.v _ _ (show -((0:ℕ):ℤ) + 0 = 0 by simp) := by
      apply free_ext
      intro U x
      exact h U x
    have := congrArg (fun φ => (chainsXIso R (sch.obj X) 0).hom ≫ φ) key
    simpa using this
  · apply IsZero.eq_of_src
    apply HomologicalComplex.isZero_extend_X
    intro i hi
    change -(i:ℤ) = q at hi
    omega

theorem CocEq_of : CocEq := cocEq

end LateralTheory.EtaleTrace
end
end
end

-- Source module: Development.EtaleCohomology.EtaleTrace.PtCovPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.EtaleTrace

theorem exists_ratPt_of_etale (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} (p : X ⟶ S k)
    (hp : IsProper p) {U : Scheme.{0}} (f : U ⟶ X) [Etale f] (x : U) :
    ∃ w : S k ⟶ U, w ≫ f ≫ p = 𝟙 _ := by
  have := hp
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  have hopen : IsOpen (Set.range f) := f.isOpenMap.isOpen_range
  obtain ⟨y, ⟨x', rfl⟩, hy⟩ := nonempty_inter_closedPoints (show (Set.range f).Nonempty from ⟨f x, x, rfl⟩) hopen.isLocallyClosed
  let s : S k ⟶ X := pointOfClosedPoint p (f x') hy
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed f s x' (pointOfClosedPoint_apply p (f x') hy _).symm
  exact ⟨l, by rw [reassoc_of% hl]; exact pointOfClosedPoint_comp p (f x') hy⟩

theorem PtCov_of : PtCov := by
  intro k _ _ X p hp Sv hSv
  obtain ⟨𝒰, h𝒰⟩ := Scheme.mem_grothendieckTopology_iff.1 hSv
  let T : Sieve X :=
    { arrows := fun V g => ∃ (U : Scheme.{0}) (g' : U ⟶ X) (h : V ⟶ U),
        Sv.arrows g' ∧ h ≫ g' = g ∧ ∃ w : S k ⟶ U, w ≫ g' ≫ p = 𝟙 _
      downward_closed := by
        rintro V W g ⟨U, g', h, hg', rfl, w, hw⟩ a
        exact ⟨U, g', a ≫ h, hg', by simp, w, hw⟩ }
  refine ⟨T, ?_, fun V g hg => hg⟩
  have hG : Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f) ∈ Scheme.etaleTopology X :=
    Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩
  refine (Scheme.etaleTopology).transitive hG T ?_
  rintro Z _ ⟨W, a, b, hb, rfl⟩
  rw [Sieve.pullback_comp]
  refine (Scheme.etaleTopology).pullback_stable a ?_
  obtain ⟨i⟩ := hb
  by_cases hne : Nonempty (𝒰.X i)
  · obtain ⟨x⟩ := hne
    obtain ⟨w, hw⟩ := exists_ratPt_of_etale k p hp (𝒰.f i) x
    have : T.arrows (𝒰.f i) := ⟨𝒰.X i, 𝒰.f i, 𝟙 _, h𝒰 _ _ (Presieve.ofArrows.mk i), by simp, w, hw⟩
    rw [Sieve.pullback_eq_top_of_mem T this]
    exact (Scheme.etaleTopology).top_mem _
  · have : IsEmpty (𝒰.X i) := not_nonempty_iff.1 hne
    exact (Scheme.etaleTopology).superset_covering bot_le (Scheme.bot_mem_grothendieckTopology _)

end LateralTheory.EtaleTrace
end
end
end

-- Source module: Development.EtaleCohomology.EtaleTrace.TorsionH0PointOfTwistCoverCocycle

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CochainComplex.HomComplex Opposite

namespace LateralTheory.EtaleTrace

theorem freeGen_nat (R : Type) [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have h := congrArg (fun f => f.hom (ModuleCat.freeMk (ULift.up x : uliftFunctor.{1, 0}.obj (P.obj (op U)))))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h
  simp only [Sec.res, freeGen]
  refine h.symm.trans ?_
  exact congrArg (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)))
    (by simp only [freeP, ModuleCat.freeMk, ModuleCat.free, Functor.comp_obj, Functor.whiskeringRight_obj_obj, Functor.comp_map]
        exact Finsupp.mapDomain_single)

theorem evNat : EvNat := by
  intro R _ F X U α x
  have h := freeGen_nat R ((sch.obj X).obj (op (SimplexCategory.mk 0))) x (𝟙 X : Sx (sch.obj X) 0 X)
  have hx : ((sch.obj X).obj (op (SimplexCategory.mk 0))).map x.op (𝟙 X : Sx (sch.obj X) 0 X) = (x : Sx (sch.obj X) 0 U) :=
    Category.comp_id x
  rw [hx] at h
  simp only [ev]
  rw [← h]
  simp only [Sec.res]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← NatTrans.naturality]

end LateralTheory.EtaleTrace
end
end
end

-- Source module: Development.EtaleCohomology.EtaleTrace.TwZeroPfSplit

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite

namespace LateralTheory.EtaleTrace

theorem tz_isUnit_ι (X : Scheme.{0}) (f : Γ(X, ⊤)) : IsUnit ((X.basicOpen f).ι.appTop.hom f) := by
  have h := RingedSpace.isUnit_res_basicOpen X.toRingedSpace f
  rw [Scheme.Opens.ι_appTop]
  have e1 : (X.basicOpen f).ι ''ᵁ ⊤ = X.basicOpen f := by simp
  have key : ∀ (W : X.Opens) (_ : W = X.basicOpen f) (hle : W ≤ ⊤), IsUnit ((X.presheaf.map (homOfLE hle).op).hom f) := by
    rintro W rfl hle
    exact h
  exact key _ e1 _

theorem tz_idem_one {A : Type} [CommRing A] {x : A} (h : IsIdempotentElem x) (hu : IsUnit x) : x = 1 := by
  obtain ⟨u, rfl⟩ := hu
  have := congrArg (· * ((u⁻¹ : Aˣ) : A)) h.eq
  simpa [mul_assoc] using this

theorem splitLoc : SplitLoc := by
  intro U n e he hs
  let W : Fin n → U.Opens := fun i => U.basicOpen (e i)
  have hW : TopologicalSpace.IsOpenCover W := by
    refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.2 fun x _ => ?_)
    rw [TopologicalSpace.Opens.mem_iSup]
    by_contra hx
    push Not at hx
    have hm : ∀ i, U.presheaf.germ ⊤ x trivial (e i) ∈ IsLocalRing.maximalIdeal (U.presheaf.stalk x) := fun i =>
      (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 ((Scheme.mem_basicOpen_top _ _ x).not.1 (hx i)))
    have hsum := Ideal.sum_mem (IsLocalRing.maximalIdeal _) (t := Finset.univ) (fun i _ => hm i)

    rw [← map_sum, hs, map_one] at hsum
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 hsum)
  let 𝒰 := U.openCoverOfIsOpenCover W hW
  refine ⟨Sieve.ofArrows 𝒰.X 𝒰.f, ?_, ?_⟩
  · exact Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology 𝒰)
  · rintro V g ⟨Y, h, f, ⟨i⟩, rfl⟩
    let j : Fin n := i
    refine ⟨j, ?_⟩
    have h1 : (W j).ι.appTop.hom (e i) = 1 := tz_idem_one ((he j).map _) (tz_isUnit_ι U (e j))
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    change h.appTop.hom ((W j).ι.appTop.hom (e j)) = 1
    rw [h1]; exact map_one _

theorem TwZero_of_split (hTw : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hS : PrimSplit) : TwZero :=
  TwZero_of hTw hS splitLoc

end LateralTheory.EtaleTrace
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PLowTL

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CochainComplex.HomComplex

namespace UpperTheory.Gal.KunnethLefschetz

private theorem twLoc : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc :=
  LateralTheory.EtaleFoundations.TwLocPf.TwLoc_of
    (LateralTheory.EtaleFoundations.TwSecLocPf.TwSecLoc_of_alg LateralTheory.EtaleFoundations.AlgPowPf.AlgPow_of)
    LateralTheory.EtaleFoundations.TwTorsPf.TwTors_of

private theorem twZero : TwZero := TwZero_of_split twLoc PrimSplit_of

private theorem lowSec : EtaleTateTwistSectionsDeterminedByPointsOfProper := tateTwistSections_determinedByPoints_of_constant twLoc PtCov_of (tateTwistSection_constantOnPoints_of_twLoc_ptCov twLoc PtCov_of)

private theorem exists_ofRings_sec_eq_twF_zero (k : Type) [Field k] [IsAlgClosed k] (q : ℕ) (s : Sec (tw q 0) (S k)) :
    ∃ t, ofRings.sec (twF q 0) (S k) t = s := by
  have h := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)) s
  obtain ⟨t, ht⟩ := PtCover_of k _ h
  refine ⟨t, ht.trans ?_⟩
  simp
  rfl

private theorem ofRings_sec_twF_zero_injective (k : Type) [Field k] [IsAlgClosed k] (q : ℕ)
    (t1 t2 : ToType ((Scheme.Γ ⋙ twF q 0).obj (Opposite.op (S k))))
    (h : ofRings.sec (twF q 0) (S k) t1 = ofRings.sec (twF q 0) (S k) t2) : t1 = t2 := by
  have h2 := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)) t1 t2 h
  have h3 := PtCover_of k _ h2
  have h4 : (Scheme.Γ ⋙ twF q 0).map (𝟙 (Opposite.op (S k))) t1 =
      (Scheme.Γ ⋙ twF q 0).map (𝟙 (Opposite.op (S k))) t2 := h3
  rwa [CategoryTheory.Functor.map_id, ModuleCat.id_apply, ModuleCat.id_apply] at h4

private theorem res_twGen_zero_eq_twGen_prim_map {q : ℕ} {U V : Scheme.{0}} (x : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res x (twGen 0 ζ) = twGen 0 (Prim.map (Scheme.Γ.map x.op).hom ζ) := by
  have hn := congrArg (fun φ => (ModuleCat.Hom.hom φ)
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Scheme.Γ ⋙ twF q 0).obj (Opposite.op U)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).naturality x.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hn
  refine hn.symm.trans ?_
  refine congrArg (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).app (Opposite.op V))) ?_
  exact congrArg Submodule.Quotient.mk Finsupp.mapDomain_single

private theorem exists_nsmul_eq_of_single_one_eq {q : ℕ} [NeZero q] {P N : Type*} [AddCommGroup N] [Module (ULift.{1, 0} (ZMod q)) N]
    (φ : (P →₀ ULift.{1, 0} (ZMod q)) →ₗ[ULift.{1, 0} (ZMod q)] N) (g0 : N)
    (h : ∀ ξ, φ (Finsupp.single ξ 1) = g0) (f : P →₀ ULift.{1, 0} (ZMod q)) :
    ∃ n : ℕ, φ f = n • g0 := by
  induction f using Finsupp.induction with
  | zero => exact ⟨0, by simp⟩
  | single_add ξ c g _ _ ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨c.down.val + n, ?_⟩
    have hc : c = ((c.down.val : ℕ) : ULift.{1, 0} (ZMod q)) := by
      apply ULift.ext
      rw [ULift.down_natCast, ZMod.natCast_zmod_val]
    calc φ (Finsupp.single ξ c + g) = c • g0 + n • g0 := by
          rw [map_add (f := _), ← Finsupp.smul_single_one, map_smul, h, hn]
      _ = (c.down.val + n) • g0 := by
          rw [add_nsmul, ← Nat.cast_smul_eq_nsmul (ULift.{1, 0} (ZMod q)) c.down.val, ← hc]

private theorem sec_res_sec_map_comm {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (k : V ⟶ U)
    (b : Sec F U) : Sec.res k (Sec.map φ b) = Sec.map φ (Sec.res k b) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

private theorem lowPt (hA : A9) (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k] (hl : (l : k) ≠ 0) (j : ℕ) :
    (∀ z : Ht (l ^ j) (sch.obj (S k)) 0 0, ∃ a : ℕ, z = a • one (l ^ j) (sch.obj (S k))) ∧
      ∀ a : ℕ, a • one (l ^ j) (sch.obj (S k)) = 0 → l ^ j ∣ a := by
  haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨_, e, _, he2⟩ := hA (ZMod (l ^ j)) (tw (l ^ j) 0)
  obtain ⟨ζ0⟩ := exists_prim l k hl j
  let φ : ((Prim (l ^ j) Γ(S k, ⊤)) →₀ ULift.{1, 0} (ZMod (l ^ j))) →ₗ[ULift.{1, 0} (ZMod (l ^ j))]
      Sec (tw (l ^ j) 0) (S k) :=
    (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF (l ^ j) 0)).app
      (Opposite.op (S k)))).comp (twRel (l ^ j) 0 Γ(S k, ⊤)).mkQ
  have hone : one (l ^ j) (sch.obj (S k)) = e (S k) (twGen 0 ζ0) := by
    obtain ⟨α, hα, hev⟩ := he2 (S k) (twGen 0 ζ0)
    have hnat : ∀ (U : Scheme.{0}) (x : Sx (sch.obj (S k)) 0 U) (ζ : Prim (l ^ j) Γ(U, ⊤)),
        ev (α : Cochain _ _ 0) 0 0 (by simp) U x = resGen 0 ζ := by
      intro U x ζ
      rw [evNat (ZMod (l ^ j)) (tw (l ^ j) 0) (S k) U (α : Cochain _ _ 0) x, hev]
      refine (sec_res_sec_map_comm (resι (ZMod (l ^ j)) (tw (l ^ j) 0)) (x : U ⟶ S k) (twGen 0 ζ0)).trans ?_
      exact congrArg (Sec.map (resι (ZMod (l ^ j)) (tw (l ^ j) 0)))
        ((res_twGen_zero_eq_twGen_prim_map (x : U ⟶ S k) ζ0).trans (twZero (l ^ j) U _ ζ))
    have h1 := pick_spec (show ∃ c, (fun c => ∃ β : Cocycle ((chains (ZMod (l ^ j))).obj (sch.obj (S k)))
        (res (ZMod (l ^ j)) (tw (l ^ j) 0)) 0, CohomologyClass.mk β = c ∧
          ∀ (U : Scheme) (x : Sx (sch.obj (S k)) 0 U) (ζ : Prim (l ^ j) Γ(U, ⊤)),
            ev (β : Cochain _ _ 0) 0 0 (by simp) U x = resGen 0 ζ) c from ⟨_, α, hα, hnat⟩)
    obtain ⟨β, hβ, hβev⟩ := h1
    refine hβ.symm.trans ((congrArg CohomologyClass.mk (CocEq_of _ _ _ β α (fun U x => ?_))).trans hα)
    exact (hβev U x (Prim.map (Scheme.Γ.map x.op).hom ζ0)).trans (hnat U x _).symm
  refine ⟨fun z => ?_, fun a ha => ?_⟩
  · obtain ⟨t, ht⟩ := exists_ofRings_sec_eq_twF_zero k (l ^ j) ((e (S k)).symm z)
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (twRel (l ^ j) 0 Γ(S k, ⊤)) t
    obtain ⟨n, hn⟩ := exists_nsmul_eq_of_single_one_eq φ (twGen 0 ζ0)
      (fun ξ => (show φ (Finsupp.single ξ 1) = twGen 0 ζ0 from twZero (l ^ j) (S k) ξ ζ0)) f
    refine ⟨n, ?_⟩
    have hf : φ f = (e (S k)).symm z := ht
    rw [hone, ← map_nsmul, ← hn, hf, AddEquiv.apply_symm_apply]
  · rw [hone, ← map_nsmul] at ha
    have hs : a • twGen 0 ζ0 = (0 : Sec (tw (l ^ j) 0) (S k)) :=
      (e (S k)).injective (ha.trans (map_zero _).symm)
    have h3 : (Submodule.Quotient.mk (a • Finsupp.single ζ0 (1 : ULift.{1, 0} (ZMod (l ^ j)))) :
        (_ ⧸ twRel (l ^ j) 0 Γ(S k, ⊤))) = Submodule.Quotient.mk 0 :=
      ofRings_sec_twF_zero_injective k (l ^ j) _ _ (show φ (a • Finsupp.single ζ0 1) = φ 0 by
        rw [map_nsmul, map_zero]
        exact hs)
    have h4 := (Submodule.Quotient.mk_eq_zero _).1 (h3.trans (Submodule.Quotient.mk_zero _))
    let ψ := Finsupp.linearCombination (ULift.{1, 0} (ZMod (l ^ j)))
      (fun _ : Prim (l ^ j) Γ(S k, ⊤) => (1 : ULift.{1, 0} (ZMod (l ^ j))))
    have hker : twRel (l ^ j) 0 Γ(S k, ⊤) ≤ LinearMap.ker ψ := by
      rw [twRel, Submodule.span_le]
      rintro x ⟨ζ, ξ, b, -, rfl⟩
      simp [ψ]
      exact sub_self (1 : ULift.{1, 0} (ZMod (l ^ j)))
    have h5 : ψ (a • Finsupp.single ζ0 1) = 0 := hker h4
    have h6 : ((a : ZMod (l ^ j))) = 0 := by
      have := congrArg ULift.down h5
      simpa [ψ] using this
    exact (ZMod.natCast_eq_zero_iff a (l ^ j)).1 h6

theorem lowTL_holds : LowTL := by
  intro hIn l _ k _ _ hl j
  obtain ⟨_, e, he1, _⟩ := (In.a9 hIn) (ZMod (l ^ j)) (tw (l ^ j) 0)
  refine ⟨lowPt (In.a9 hIn) l k hl j, ?_⟩
  intro X p hp z
  have hz : ∀ y : Pt p, pull (ZMod (l ^ j)) (sch.map y.1) (tw (l ^ j) 0) 0 z =
      e (S k) (Sec.res y.1 ((e X).symm z)) := by
    intro y
    rw [← he1, AddEquiv.apply_symm_apply]
  obtain ⟨h1, h2⟩ := lowSec l k hl j p hp ((e X).symm z)
  refine ⟨fun hy => ?_, fun hc y y' => ?_⟩
  · have h0 : (e X).symm z = 0 :=
      h1 (fun y => (e (S k)).injective (by rw [← hz, hy y, map_zero]))
    have := congrArg (e X) h0
    rwa [AddEquiv.apply_symm_apply, map_zero] at this
  · rw [hz, hz, h2 hc y y']

end UpperTheory.Gal.KunnethLefschetz
end
end
end
