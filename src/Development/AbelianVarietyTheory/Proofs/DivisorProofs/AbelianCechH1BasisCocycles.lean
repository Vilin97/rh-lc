module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeStructureSheafCohomologyNoetherianStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCapFBijective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechToPosetPosetToCechSubCoboundaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCocyclePosetOneCochainToCechCochainStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosetToCechCechToPosetCocycleEqStatement
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechOneCochainToPosetCochainCoboundaryExists

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

namespace GlobalTheory.CechCmp

theorem cechOneCochainToPosetCochain_coboundary_exists : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R)
    (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)),
    ∀ c : GlobalTheory.KS.C1 U, IsCob U c → ∃ g, d0 (capF s U hU hinf) g = toPos s U hU hinf c := by
  intro I _ X R _ s U hU hinf c hc
  obtain ⟨b, hb⟩ := hc
  refine ⟨fun T => (cv s U hU hinf T).symm (rsT (b T.unop.pt) (cap U T.unop)), ?_⟩
  funext T T' φ
  apply (cv s U hU hinf T').injective
  have hTT' : cap U T'.unop ≤ cap U T.unop := cap_mono U (leOfHom φ.unop)
  have hp : cap U T.unop ≤ U T.unop.pt := cap_le U T.unop.pt_mem
  have hp' : cap U T'.unop ≤ U T'.unop.pt := cap_le U T'.unop.pt_mem
  have hle : cap U T'.unop ≤ U T.unop.pt ⊓ U T'.unop.pt := le_inf (hTT'.trans hp) hp'
  rw [amitsur_d0_apply, map_sub, cv_mp, cv_toPos, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hb,
    GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_rsT inf_le_right hle, GlobalTheory.KS.rsT_rsT inf_le_left hle, GlobalTheory.KS.rsT_rsT hp hTT']

end GlobalTheory.CechCmp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechOneCochainToPosetCochainCoboundaryExistsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

theorem _root_.GlobalTheory.T.exists_d0_eq_toPos_of_isCob : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ c : GlobalTheory.KS.C1 U, IsCob U c → ∃ g, d0 (capF s U hU hinf) g = toPos s U hU hinf c := by
  first | exact @GlobalTheory.CechCmp.cechOneCochainToPosetCochain_coboundary_exists | exact GlobalTheory.CechCmp.cechOneCochainToPosetCochain_coboundary_exists | (intros; apply GlobalTheory.CechCmp.cechOneCochainToPosetCochain_coboundary_exists <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechOneCochainToPosetCochainMemCocycles

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

namespace GlobalTheory.CechCmp

theorem cechOneCochainToPosetCochain_mem_cocycles : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ c : GlobalTheory.KS.C1 U, IsCoc U c → toPos s U hU hinf c ∈ Z1 (capF s U hU hinf) := by
  intro I _ X R _ s U hU hinf c hc T T' T'' φ ψ
  have h1 : T.unop.set ⊆ T'.unop.set := NE.le_iff.1 (leOfHom φ.unop)
  have h2 : T'.unop.set ⊆ T''.unop.set := NE.le_iff.1 (leOfHom ψ.unop)
  have ha : T.unop.pt ∈ T''.unop.set := h2 (h1 T.unop.pt_mem)
  have hb : T'.unop.pt ∈ T''.unop.set := h2 T'.unop.pt_mem
  have ha' : T.unop.pt ∈ T'.unop.set := h1 T.unop.pt_mem
  have hW : cap U T''.unop ≤ U T.unop.pt ⊓ U T'.unop.pt ⊓ U T''.unop.pt :=
    le_inf (le_inf (cap_le U ha) (cap_le U hb)) (cap_le U T''.unop.pt_mem)
  have hT' : cap U T'.unop ≤ U T.unop.pt ⊓ U T'.unop.pt := le_inf (cap_le U ha') (cap_le U T'.unop.pt_mem)
  have h23 : cap U T''.unop ≤ cap U T'.unop := cap_mono U (leOfHom ψ.unop)
  have key := congrArg (fun x => rsT x (cap U T''.unop)) (hc T.unop.pt T'.unop.pt T''.unop.pt)
  simp only [GlobalTheory.KS.rsT_add] at key
  have e1 : U T.unop.pt ⊓ U T'.unop.pt ⊓ U T''.unop.pt ≤ U T.unop.pt ⊓ U T'.unop.pt := inf_le_left
  have e2 : U T.unop.pt ⊓ U T'.unop.pt ⊓ U T''.unop.pt ≤ U T'.unop.pt ⊓ U T''.unop.pt :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have e3 : U T.unop.pt ⊓ U T'.unop.pt ⊓ U T''.unop.pt ≤ U T.unop.pt ⊓ U T''.unop.pt :=
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  rw [GlobalTheory.KS.rsT_rsT e1 hW, GlobalTheory.KS.rsT_rsT e2 hW, GlobalTheory.KS.rsT_rsT e3 hW] at key
  apply (cv s U hU hinf T'').injective
  rw [map_add (f := _), cv_toPos, cv_mp, cv_toPos, cv_toPos, GlobalTheory.KS.rsT_rsT hT' h23]
  exact key.symm

end GlobalTheory.CechCmp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechOneCochainToPosetCochainMemCocyclesStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

theorem _root_.GlobalTheory.T.toPos_mem_Z1_of_isCoc : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ c : GlobalTheory.KS.C1 U, IsCoc U c → toPos s U hU hinf c ∈ Z1 (capF s U hU hinf) := by
  first | exact @GlobalTheory.CechCmp.cechOneCochainToPosetCochain_mem_cocycles | exact GlobalTheory.CechCmp.cechOneCochainToPosetCochain_mem_cocycles | (intros; apply GlobalTheory.CechCmp.cechOneCochainToPosetCochain_mem_cocycles <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosetOneCochainToCechCochainCoboundary

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

noncomputable section

namespace GlobalTheory.CechCmp

theorem posetOneCochainToCechCochain_coboundary : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ g : C0 (capF s U hU hinf), IsCob U (toCech s U hU hinf (d0 (capF s U hU hinf) g)) := by
  intro I _ X R _ s U hU hinf g
  refine ⟨fun i => rsT (cv s U hU hinf (op (NE.single i)) (g (op (NE.single i)))) (U i), fun i j => ?_⟩
  have hp : U i ⊓ U j ≤ cap U (NE.pair i j) := (cap_pair U i j).ge
  have key : ∀ k, k ∈ ({i, j} : Set I) →
      rsT (rsT (cv s U hU hinf (op (NE.single k)) (g (op (NE.single k)))) (cap U (NE.pair i j))) (U i ⊓ U j) =
        rsT (rsT (cv s U hU hinf (op (NE.single k)) (g (op (NE.single k)))) (U k)) (U i ⊓ U j) := by
    intro k hk
    have hk' : U i ⊓ U j ≤ U k := by
      rcases hk with rfl | hk
      · exact inf_le_left
      · rw [Set.mem_singleton_iff.1 hk]; exact inf_le_right
    rw [GlobalTheory.KS.rsT_rsT (cap_mono U (a := NE.pair i j) (b := NE.single k) (NE.le_iff.2 (by rw [NE.set_single, NE.set_pair]; exact Set.singleton_subset_iff.2 hk))) hp,
      GlobalTheory.KS.rsT_rsT (cap_single U k).ge hk']
  rw [toCech_apply, amitsur_d0_apply, amitsur_d0_apply, map_sub, map_sub, cv_mp, cv_mp, GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_sub]
  have e1 := key i (Set.mem_insert i {j})
  have e2 := key j (Set.mem_insert_of_mem i rfl)
  simp only [unop_op] at e1 e2 ⊢
  rw [e1, e2]
  abel

end GlobalTheory.CechCmp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosetOneCochainToCechCochainCoboundaryStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

theorem _root_.GlobalTheory.T.isCob_toCech_d0 : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ g : C0 (capF s U hU hinf), IsCob U (toCech s U hU hinf (d0 (capF s U hU hinf) g)) := by
  first | exact @GlobalTheory.CechCmp.posetOneCochainToCechCochain_coboundary | exact GlobalTheory.CechCmp.posetOneCochainToCechCochain_coboundary | (intros; apply GlobalTheory.CechCmp.posetOneCochainToCechCochain_coboundary <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianCechH1BasisCocycles

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechDR (HO1)

namespace GlobalTheory.CechFree

theorem cech_free : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (I : Type) [Finite I] (U : I → B.left.Opens), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ⨆ i, U i = ⊤ → (∀ i, IsAffineOpen (U i)) → ∃ b : Fin g → C1 U, (∀ a, IsCoc U (b a)) ∧ ∀ c : C1 U, IsCoc U c → ∃! cc : Fin g → A, IsCob U (fun i j => c i j - ∑ a, constFn B.hom _ (cc a) * b a i j) := by
  intro A _ _ _ B _ _ g I _ U hA hg hcov hU
  classical
  have hinf : ∀ V W : B.left.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W) := by
    haveI := hA.proper
    have : B.left.IsSeparated := ⟨by rw [← terminal.comp_from B.hom]; infer_instance⟩
    exact fun V W hV hW => hV.inf hW
  obtain ⟨hfin, hproj, hrk⟩ := (GlobalTheory.T.abelianScheme_structureSheafCohomology_noetherian A B g hA hg).1
  haveI := hfin
  haveI := hproj
  haveI : Module.Free A (HO1 B.hom) := Module.free_of_flat_of_isLocalRing
  have hr : Module.finrank A (HO1 B.hom) = g := by
    rw [← hrk (IsLocalRing.closedPoint A), Module.rankAtStalk_eq_finrank_tensorProduct, Module.finrank_baseChange]
  let bH := Module.finBasisOfFinrankEq A (HO1 B.hom) hr
  let F := GlobalTheory.CechCmp.capF B.hom U hU hinf
  let e : HO1 B.hom ≃ₗ[A] CatCoh.H1 F :=
    LinearEquiv.ofBijective (CatCoh.CoefMap.restrict (GlobalTheory.CechDR.OAff B.hom)
      (GlobalTheory.CechCmp.capAff_mono U hU hinf).functor.op).pull1 (GlobalTheory.CechCmp.restrict_capF_bijective B.hom U hU hinf hcov)
  let bP := bH.map e
  choose f hf using fun a => CatCoh.H1.mk_surjective F (bP a)
  let b : Fin g → C1 U := fun a => GlobalTheory.CechCmp.toCech B.hom U hU hinf (f a).1
  have hb : ∀ a, IsCoc U (b a) := fun a => GlobalTheory.T.isCechOneCocycle_posetOneCochainToCechCochain I B.left A B.hom U hU hinf _ (f a).2
  have hbP : ∀ a, CatCoh.H1.mk F ⟨GlobalTheory.CechCmp.toPos B.hom U hU hinf (b a),
      GlobalTheory.T.toPos_mem_Z1_of_isCoc I B.left A B.hom U hU hinf _ (hb a)⟩ = bP a := by
    intro a
    rw [← hf a, CatCoh.H1.mk_eq_mk]
    exact GlobalTheory.T.exists_d0_eq_toPos_toCech_sub_of_mem_Z1 I B.left A B.hom U hU hinf _ (f a).2
  have hbb : ∀ a, GlobalTheory.CechCmp.toCech B.hom U hU hinf (GlobalTheory.CechCmp.toPos B.hom U hU hinf (b a)) = b a :=
    fun a => GlobalTheory.T.posetToCech_cechToPoset_cocycle_eq I B.left A B.hom U hU hinf _ (hb a)

  have hlc : ∀ (cc : Fin g → A) (hm : GlobalTheory.CechCmp.toPos B.hom U hU hinf
      (fun i j => ∑ a, constFn B.hom (U i ⊓ U j) (cc a) * b a i j) ∈ CatCoh.Z1 F),
      CatCoh.H1.mk F ⟨_, hm⟩ = ∑ a, cc a • bP a := by
    intro cc hm
    have : (⟨_, hm⟩ : CatCoh.Z1 F) = ∑ a, cc a • ⟨GlobalTheory.CechCmp.toPos B.hom U hU hinf (b a),
        GlobalTheory.T.toPos_mem_Z1_of_isCoc I B.left A B.hom U hU hinf _ (hb a)⟩ := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      exact GlobalTheory.CechCmp.toPos_lc B.hom U hU hinf cc b

    rw [this, map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, hbP]
  have hmem : ∀ cc : Fin g → A, GlobalTheory.CechCmp.toPos B.hom U hU hinf
      (fun i j => ∑ a, constFn B.hom (U i ⊓ U j) (cc a) * b a i j) ∈ CatCoh.Z1 F := by
    intro cc
    rw [GlobalTheory.CechCmp.toPos_lc]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (GlobalTheory.T.toPos_mem_Z1_of_isCoc I B.left A B.hom U hU hinf _ (hb a))
  refine ⟨b, hb, fun c hc => ?_⟩
  have hcm := GlobalTheory.T.toPos_mem_Z1_of_isCoc I B.left A B.hom U hU hinf c hc
  let x := CatCoh.H1.mk F ⟨_, hcm⟩
  have hex : IsCob U (fun i j => c i j - ∑ a, constFn B.hom (U i ⊓ U j) (bP.repr x a) * b a i j) := by
    let l : C1 U := fun i j => ∑ a, constFn B.hom (U i ⊓ U j) (bP.repr x a) * b a i j
    have hl : GlobalTheory.CechCmp.toCech B.hom U hU hinf (GlobalTheory.CechCmp.toPos B.hom U hU hinf l) = l := by
      rw [GlobalTheory.CechCmp.toPos_lc, GlobalTheory.CechCmp.toCech_lc]
      simp only [hbb, l]
    have h0 : CatCoh.H1.mk F ⟨_, hcm⟩ = CatCoh.H1.mk F ⟨_, hmem (bP.repr x)⟩ := by
      rw [hlc _ (hmem _)]
      exact (bP.sum_repr x).symm
    obtain ⟨g0, hg0⟩ := CatCoh.H1.mk_eq_mk.1 h0
    have key : (fun i j => c i j - l i j) = GlobalTheory.CechCmp.toCech B.hom U hU hinf (CatCoh.d0 F g0) := by
      rw [hg0, GlobalTheory.CechCmp.toCech_sub, GlobalTheory.T.posetToCech_cechToPoset_cocycle_eq I B.left A B.hom U hU hinf c hc, hl]
      rfl
    show IsCob U (fun i j => c i j - l i j)
    rw [key]
    exact GlobalTheory.T.isCob_toCech_d0 I B.left A B.hom U hU hinf g0
  refine ⟨bP.repr x, hex, fun cc hcc => ?_⟩
  have hcs : ∀ (O : B.left.Opens) (y z : A), constFn B.hom O (y - z) = constFn B.hom O y - constFn B.hom O z :=
    fun O y z => by simp only [constFn, map_sub]
  let δ : Fin g → A := fun a => bP.repr x a - cc a
  have hcob : IsCob U (fun i j => ∑ a, constFn B.hom (U i ⊓ U j) (δ a) * b a i j) := by
    obtain ⟨β₁, h₁⟩ := hcc
    obtain ⟨β₂, h₂⟩ := hex
    refine ⟨fun i => β₁ i - β₂ i, fun i j => ?_⟩
    have e₁ := h₁ i j
    have e₂ := h₂ i j
    simp only [δ, hcs, sub_mul, Finset.sum_sub_distrib, GlobalTheory.KS.rsT_sub] at e₁ e₂ ⊢
    linear_combination e₁ - e₂
  obtain ⟨g1, hg1⟩ := GlobalTheory.T.exists_d0_eq_toPos_of_isCob I B.left A B.hom U hU hinf _ hcob
  have hz : ∑ a, δ a • bP a = 0 := by
    rw [← hlc δ (hmem δ)]
    exact CatCoh.H1.mk_eq_zero.2 ⟨g1, hg1⟩
  have hδ := Fintype.linearIndependent_iff.1 bP.linearIndependent δ hz
  funext a
  exact (sub_eq_zero.1 (hδ a)).symm

end GlobalTheory.CechFree
end
end
end
