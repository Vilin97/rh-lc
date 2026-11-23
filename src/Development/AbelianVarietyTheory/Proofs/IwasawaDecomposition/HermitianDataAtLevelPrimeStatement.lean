module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondOperatorHermitianSideLevelPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBasisAtOfIsLocBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
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
public import Mathlib.Geometry.Euclidean.Projection
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicConjugateCharacterStandardFormsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRelationClassesCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPrimesOverLevelPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalEqOfClassesRelatedAtPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MiddleStepOneLevelProjectionEqChartProjectionStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianSeenPrimeConditionHermitianSide
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianSideClassesEqFormClassesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianUpMoveAtLevelPrimePlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MiddleStepOneLevelProjectionEqChartProjectionStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StabiliserMapHyperplaneEqConjClassMapStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualModClassLatticeEquivQuotient

section
@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.HAt.Disc

section Gen

variable {R V W : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

def quotMapEquiv (e : V ≃ₗ[R] W) (A L : Submodule R V) (A' L' : Submodule R W) (hA : A.map (e : V →ₗ[R] W) = A')
    (hL : L.map (e : V →ₗ[R] W) = L') : (A ⧸ L.comap A.subtype) ≃ₗ[R] (A' ⧸ L'.comap A'.subtype) := by
  subst hA hL
  refine Submodule.Quotient.equiv _ _ (e.submoduleMap A) ?_
  ext ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨z, hz, hze⟩
    have : (z : V) = x := e.injective (congrArg Subtype.val hze)
    exact ⟨x, this ▸ hz, rfl⟩
  · rintro ⟨x', hx', hxe⟩
    have : x' = x := e.injective hxe
    subst this
    exact ⟨⟨x', hx⟩, hx', rfl⟩

end Gen

end GlobalTheory.Mem.Col2.HAt.Disc

namespace GlobalTheory.Mem.Col2.HAt.Disc

theorem span_pi_eq {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) :
    Ideal.span {Pr.piT u} = ⨅ P : Pr.vT u, P.1.asIdeal := by
  refine le_antisymm ?_ fun r hr => ?_
  · refine le_iInf fun P => ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact decoFin_mem_of_mem_divs P.2
  · exact Ideal.mem_span_singleton.2 (piT_dvd_of_mem hX hPr u r fun P => Ideal.mem_iInf.1 hr P)

theorem span_conj_pi_eq {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) :
    Ideal.span {X.conjO (Pr.piT u)} = ⨅ P : Pr.vT u, (conjPrime₂ P.1).asIdeal := by
  refine le_antisymm ?_ fun r hr => ?_
  · refine le_iInf fun P => ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show cO X.E (X.conjO (Pr.piT u)) ∈ P.1.asIdeal
    rw [show cO X.E (X.conjO (Pr.piT u)) = Pr.piT u from cO_cO _]
    exact decoFin_mem_of_mem_divs P.2
  · obtain ⟨s, hs⟩ := piT_dvd_of_mem hX hPr u (cO X.E r) fun P => Ideal.mem_iInf.1 hr P
    refine Ideal.mem_span_singleton.2 ⟨cO X.E s, ?_⟩
    have := congrArg (cO X.E) hs
    rw [cO_cO, map_mul] at this
    exact this

end GlobalTheory.Mem.Col2.HAt.Disc

namespace GlobalTheory.Mem.Col2.HAt.Disc

theorem span_T_eq {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) :
    Ideal.span {((Pr.T u : ℕ) : 𝓞 X.E)} = Ideal.span {Pr.piT u} ⊓ Ideal.span {X.conjO (Pr.piT u)} := by
  rw [← hPr.piT_norm u, ← Ideal.span_singleton_mul_span_singleton]
  exact Ideal.mul_eq_inf_of_coprime ((Ideal.isCoprime_span_singleton_iff _ _).2 (hPr.piT_cop u)).sup_eq

theorem quotT_equiv {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) :
    Nonempty ((𝓞 X.E ⧸ Ideal.span {((Pr.T u : ℕ) : 𝓞 X.E)}) ≃ₗ[𝓞 X.E]
      ((∀ P : Pr.vT u, 𝓞 X.E ⧸ P.1.asIdeal) × (∀ P : Pr.vT u, 𝓞 X.E ⧸ (conjPrime₂ P.1).asIdeal))) := by
  have hco : IsCoprime (Ideal.span {Pr.piT u}) (Ideal.span {X.conjO (Pr.piT u)}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).2 (hPr.piT_cop u)
  have hp1 : Pairwise (Function.onFun IsCoprime fun P : Pr.vT u => P.1.asIdeal) := fun P Q hne => by
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne P.1.isMaximal Q.1.isMaximal fun h => hne (Subtype.ext (HeightOneSpectrum.ext h))
  have hp2 : Pairwise (Function.onFun IsCoprime fun P : Pr.vT u => (conjPrime₂ P.1).asIdeal) := fun P Q hne => by
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    refine Ideal.IsMaximal.coprime_of_ne (conjPrime₂ P.1).isMaximal (conjPrime₂ Q.1).isMaximal fun h => hne (Subtype.ext ?_)
    ext x
    have h2 := congrArg (fun J : Ideal (𝓞 X.E) => cO X.E x ∈ J) h
    simp only [conjPrime₂, Ideal.mem_comap, cO_cO] at h2
    exact Iff.of_eq h2
  let φ : (𝓞 X.E ⧸ Ideal.span {((Pr.T u : ℕ) : 𝓞 X.E)}) ≃+*
      ((∀ P : Pr.vT u, 𝓞 X.E ⧸ P.1.asIdeal) × (∀ P : Pr.vT u, 𝓞 X.E ⧸ (conjPrime₂ P.1).asIdeal)) :=
    (Ideal.quotEquivOfEq (span_T_eq hPr u)).trans ((Ideal.quotientInfEquivQuotientProd _ _ hco).trans
      (RingEquiv.prodCongr
        ((Ideal.quotEquivOfEq (span_pi_eq hX hPr u)).trans (Ideal.quotientInfRingEquivPiQuotient _ hp1))
        ((Ideal.quotEquivOfEq (span_conj_pi_eq hX hPr u)).trans (Ideal.quotientInfRingEquivPiQuotient _ hp2))))
  exact ⟨(AlgEquiv.ofRingEquiv (f := φ) fun a => rfl).toLinearEquiv⟩

end GlobalTheory.Mem.Col2.HAt.Disc


open GlobalTheory.Mem.Col2.HAt.Disc in
theorem GlobalTheory.Mem.Col2.TC.disc_cl : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u, DiscCl (D := I.rec7 l Z) (u := u) := by
  intro B X I hI hP l Z H F _ _ u i hi c
  obtain ⟨hG, -, hc⟩ := (spaces_in_coordinates I hI hP l Z).2.2.2 i hi
  have hL : latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c) = ((I.stp u I.mu0 i).rep c).1.1.deco.1.L := (hc u I.mu0).1 c
  have hD : lc ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (Formalism.L2.Herm.Ld (I.rec7 l Z) u i c) =
      ((I.stp u I.mu0 i).rep c).1.1.deco.1.Lsh := by
    refine (dual_co (I.rec7 l Z).sp.cm _ (rankN (I.rec7 l Z) i hi) _).trans ?_
    have h1 := BwLat.dualL_std (E := B.host.E) (sigD (I.rec7 l Z)).toRingHom (fun x => rfl) ((I.stp u I.mu0 i).rep c).1.1.deco.1.L
    exact (congrArg₂ (dualL _) hG hL).trans h1
  have hc' : ∀ P Q : (B.primes X).vT u, Q.1 ≠ conjPrime₂ P.1 := fun P Q => (moveHyp_of_ok l.pr u P).st Q
  obtain ⟨e1⟩ := ((I.stp u I.mu0 i).rep c).1.1.deco.2.Lsh_quot_L hc'
  obtain ⟨e2⟩ := quotT_equiv (FieldsLaws.fields_satisfy_definite_laws B).1.ok l.pr u
  exact ⟨(quotMapEquiv ((crdN (I.rec7 l Z) i hi).restrictScalars (𝓞 (I.rec7 l Z).host.E)) _ _ _ _ hD hL) ≪≫ₗ e1 ≪≫ₗ e2.symm⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualModClassLatticeEquivQuotientStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.dual_mod_class_lattice_equiv_quotient : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u, DiscCl (D := I.rec7 l Z) (u := u) := by
  first | exact @GlobalTheory.Mem.Col2.TC.disc_cl | exact GlobalTheory.Mem.Col2.TC.disc_cl | (intros; apply GlobalTheory.Mem.Col2.TC.disc_cl <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHermitianDownMoveAtLevelPrimePlace

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt



theorem dnCl_of_tie {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z))
    (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u))
    (hS : ∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) (hC : CarH H F) (u) (i : ℕ) (hi : i ≤ (I.rec7 l Z).R.m) (v)
    (c : ((I.rec7 l Z).mem u).C.cls i)
    (g : Module.Dual (((I.rec7 l Z).mem u).A.Fv v) (((I.rec7 l Z).fm u).lk i v c))
    (γ₀ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi))
    (hAd : AdC (F u) i hi c (((I.rec7 l Z).fm u).dn i v c g) γ₀.1 ((F u).atT.eV v).1)
    (hloc : Formalism.HermitianLatticesTheory.localization₂ ((F u).atT.Pv v) (Formalism.L2.Forms.mulLat γ₀.1.1
        (Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi (((I.rec7 l Z).fm u).dn i v c g))) =
      Formalism.HermitianLatticesTheory.localization₂ ((F u).atT.Pv v) (clsCrd (I.rec7 l Z) u i hi c))
    (hfv : ∀ (x : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi (((I.rec7 l Z).fm u).dn i v c g))
      (hx : γ₀.1.1 *ᵥ x.1 ∈ Formalism.L2.Forms.Lk (F u).atT i hi v c),
      ((I.rec7 l Z).fm u).fv i v _ (((F u).lv i hi).pr v _ x) = g (((F u).lv i hi).prk v c ⟨_, hx⟩)) :
    DnCl (F u).atT (F u).lv i v c g (gx i hi γ₀) ∧
      AdOf H u i c (((I.rec7 l Z).fm u).dn i v c g) (gx i hi γ₀) v := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, GlobalTheory.T.adelic_relation_classes_coordinates I hOk hP l Z H F hS hC u i hi v c _ γ₀ hAd⟩
  · intro q hq hq1 hq2
    haveI := hq.isPrime
    let Q : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E) :=
      ⟨q, hq.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hq (RingOfIntegers.not_isField _)⟩
    have hu : Q.under (𝓞 (I.rec7 l Z).host.F) ≠ ((F u).atT.eV v).1 := fun h =>
      (GlobalTheory.T.host_primes_over_level_place I hOk hP l Z H F hS hC u v Q h).elim hq1 hq2
    have h1 := GlobalTheory.T.adelic_conjugate_character_standard_forms I hOk hP l Z H F hS hC u i hi v c _ γ₀.1 hAd Q hu
    refine Submodule.map_injective_of_injective
      (f := ((crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X i).V →ₗ[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E] (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N i) → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)).restrictScalars (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)))
      (crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi).injective ?_
    rw [localization_map₂ hi, localization_map₂ hi, lc_gmap]
    exact h1
  · have e : lc ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (Formalism.L2.Herm.Ld (I.rec7 l Z) u i (((I.rec7 l Z).fm u).dn i v c g)) =
        Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi (((I.rec7 l Z).fm u).dn i v c g) :=
      dual_co (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) ((I.rec7 l Z).clsLat u i _)
    refine Submodule.map_injective_of_injective
      (f := ((crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X i).V →ₗ[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E] (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N i) → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)).restrictScalars (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)))
      (crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi).injective ?_
    rw [localization_map₂ hi, localization_map₂ hi, lc_gmap]
    refine Eq.trans ?_ hloc
    exact congrArg (fun L => Formalism.HermitianLatticesTheory.localization₂ ((F u).atT.Pv v) (Formalism.L2.Forms.mulLat γ₀.1.1 L)) e
  · intro z hz
    rw [prH_eq _ _ hi, prkH_eq _ _ hi]
    have hx : γ₀.1.1 *ᵥ (toLd i hi _ z).1 ∈ Formalism.L2.Forms.Lk (F u).atT i hi v c := by
      rw [show (toLd i hi _ z).1 = crdN (I.rec7 l Z) i hi z.1 from rfl, ← crdN_gx]
      exact (mem_Lk (F u).atT i hi v c _).1 hz
    rw [hfv _ hx]
    exact congrArg g (congrArg _ (Subtype.ext (crdN_gx i hi γ₀ z.1).symm))
  · intro v' hv' z hz
    rw [prH_eq _ _ hi, prH_eq _ _ hi]
    exact GlobalTheory.T.levelFunctional_eq_of_classes_related_at_place I hOk hP l Z H F hS hC u i hi v v' c _ γ₀.1 hAd hv' (toLd i hi c ⟨_, hz⟩) (toLd i hi _ z)
      (crdN_gx i hi γ₀ z.1)

end GlobalTheory.Mem.Col2.HAt



theorem GlobalTheory.Mem.Col2.HAt.dn_move_exists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i v (c : ((I.rec7 l Z).mem u).C.cls i) (g : Module.Dual (((I.rec7 l Z).mem u).A.Fv v) (((I.rec7 l Z).fm u).lk i v c)), ∃ γ, i ≤ (I.rec7 l Z).R.m → g ≠ 0 → DnCl (F u).atT (F u).lv i v c g γ ∧ AdOf H u i c (((I.rec7 l Z).fm u).dn i v c g) γ v := by
  intro B X I hOk hP l Z H F hS hC u i v c g
  by_cases hcase : i ≤ (I.rec7 l Z).R.m ∧ g ≠ 0
  · obtain ⟨hi, hg⟩ := hcase
    by_cases hN : i = 0 ∨ i = (I.rec7 l Z).R.m
    · obtain ⟨γ, η, κ, hη, hy, hloc, hfv, -⟩ := (F u).dnN i hi hN v c g hg
      refine ⟨gx i hi γ, fun _ _ => dnCl_of_tie I hOk hP l Z H F hS hC u i hi v c g γ
        ⟨fun _ => ⟨κ.1, κ.2, η.1, η.2, hη, hy⟩, fun h1 h2 => absurd hN (by omega)⟩ hloc hfv⟩
    · have h1 : 1 ≤ i := by omega
      have h2 : i + 1 ≤ (I.rec7 l Z).R.m := by omega
      obtain ⟨hβ, γ, η, κ, hη, hy, hloc, hfv, -⟩ := (F u).dnC i h1 h2 v (H.chOf u i c) ⟨c, rfl⟩ g hg
      refine ⟨gx i hi γ, fun _ _ => dnCl_of_tie I hOk hP l Z H F hS hC u i hi v c g γ
        ⟨fun h => absurd h hN, fun _ _ => ⟨hβ, κ.1, κ.2, η.1, η.2, hη, hy⟩⟩ hloc ?_⟩
      intro x hx
      rw [← (GlobalTheory.T.middleStep_oneLevel_projection_eq_chart_projection I hOk hP l Z H F hS hC u i h1 h2 v (((I.rec7 l Z).fm u).dn i v c g)).1 x x rfl,
        ← (GlobalTheory.T.middleStep_oneLevel_projection_eq_chart_projection I hOk hP l Z H F hS hC u i h1 h2 v c).2 ⟨_, hx⟩ ⟨_, hx⟩ rfl]
      exact hfv x hx
  · exact ⟨1, fun hi hg => absurd ⟨hi, hg⟩ hcase⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHermitianDownMoveAtLevelPrimePlaceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_hermitianDownMove_at_levelPrime_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i v (c : ((I.rec7 l Z).mem u).C.cls i) (g : Module.Dual (((I.rec7 l Z).mem u).A.Fv v) (((I.rec7 l Z).fm u).lk i v c)), ∃ γ, i ≤ (I.rec7 l Z).R.m → g ≠ 0 → DnCl (F u).atT (F u).lv i v c g γ ∧ AdOf H u i c (((I.rec7 l Z).fm u).dn i v c g) γ v := by
  first | exact @GlobalTheory.Mem.Col2.HAt.dn_move_exists | exact GlobalTheory.Mem.Col2.HAt.dn_move_exists | (intros; apply GlobalTheory.Mem.Col2.HAt.dn_move_exists <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianSeenPrimeConditionHermitianSideStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.hermitianSeenPrimeCondition_hermitianSide : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u, SeenCl (F u).atT := by
  first | exact @GlobalTheory.Mem.Col2.HAt.seenCl_atT | exact GlobalTheory.Mem.Col2.HAt.seenCl_atT | (intros; apply GlobalTheory.Mem.Col2.HAt.seenCl_atT <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianDataAtLevelPrime

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section


theorem GlobalTheory.Mem.Col2.TC.hermitian_data_at_level_prime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∃ A, CarT H F A ∧ Formalism.L2.Herm.SymmetricAdelicCompatibility (I.rec7 l Z) H A ∧ Formalism.L2.Herm.SymmetricStabilizerMapCompatibility (I.rec7 l Z) H A := by
  intro B X I hI hP l Z H F hS hC
  have hseen := GlobalTheory.T.hermitianSeenPrimeCondition_hermitianSide I hI hP l Z H F hS hC
  have hdisc := GlobalTheory.T.dual_mod_class_lattice_equiv_quotient I hI hP l Z H F hS hC
  have hlvc := GlobalTheory.T.middleStep_oneLevel_projection_eq_chart_projection I hI hP l Z H F hS hC
  have hstab := GlobalTheory.T.stabiliserMap_hyperplane_eq_conj_classMap I hI hP l Z H F hS hC
  choose upG hup using GlobalTheory.T.hermitianUpMove_at_levelPrime_place I hI hP l Z H F hS hC
  choose dnG hdn using GlobalTheory.T.exists_hermitianDownMove_at_levelPrime_place I hI hP l Z H F hS hC
  choose dilG hdil using GlobalTheory.T.diamondOperator_hermitian_side_levelPrime I hI hP l Z H F hS hC
  choose lattice₂ levP clsP hcar hlat using GlobalTheory.T.hermitianSide_classes_eq_formClasses I hI hP l Z H F hS hC
  let A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u) := fun u =>
    mkAtT (F u).atT (F u).lv (hC.eV u) (hC.fv u) (hseen u) (hdisc u) (upG u) (fun i hi v c y h => (hup u i v c y hi h).1)
      (dnG u) (fun i hi v c g h => (hdn u i v c g hi h).1) (dilG u) (fun i hi v a c => (hdil u i v a c hi).1)
      (lattice₂ u) (levP u) (clsP u) (F u).til (hlat u)
  have hT : CarT H F A := by
    refine ⟨fun _ => rfl, fun _ => rfl, hcar, hlat, ?_, ?_, ?_, ?_, ?_⟩
    · intro u i hi v c z z' h
      exact (congrArg _ (Subtype.ext h)).trans (prH_eq (F u).atT (F u).lv hi v c z).symm
    · intro u i hi v c z z' h
      exact (congrArg _ (Subtype.ext h)).trans (prkH_eq (F u).atT (F u).lv hi v c z).symm
    · intro u i h1 h2 v c z z' h
      refine ((hlvc u i h1 h2 v c).1 (toLd i (le_of_succ_m h2) c z) z' h).trans (prH_eq (F u).atT (F u).lv (le_of_succ_m h2) v c z).symm
    · intro u
      exact ((crdN (I.rec7 l Z) _ le_rfl).apply_symm_apply _).symm
    · intro u c
      exact (reGL_lin _ (rankN (I.rec7 l Z) _ le_rfl) _).symm
  refine ⟨A, hT, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hstab A hT⟩
  · intro u v c y h
    exact (hup u 0 v c y (Nat.zero_le _) h).2
  · intro u i h1 hm v c y h
    cases i with
    | zero => omega
    | succ i => exact (hup u (i + 1) v c y hm h).2 hm
  · intro u v c g h
    exact (hdn u 0 v c g (Nat.zero_le _) h).2
  · intro u i h1 hm v c g h
    cases i with
    | zero => omega
    | succ i => exact (hdn u (i + 1) v c g hm h).2 hm
  · intro u v a c
    exact (hdil u 0 v a c (Nat.zero_le _)).2
  · intro u i h1 hm v a c
    cases i with
    | zero => omega
    | succ i => exact (hdil u (i + 1) v a c hm).2 hm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianDataAtLevelPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_hermitian_data_carT_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∃ A, CarT H F A ∧ Formalism.L2.Herm.SymmetricAdelicCompatibility (I.rec7 l Z) H A ∧ Formalism.L2.Herm.SymmetricStabilizerMapCompatibility (I.rec7 l Z) H A := by
  first | exact @GlobalTheory.Mem.Col2.TC.hermitian_data_at_level_prime | exact GlobalTheory.Mem.Col2.TC.hermitian_data_at_level_prime | (intros; apply GlobalTheory.Mem.Col2.TC.hermitian_data_at_level_prime <;> assumption)
end
end
