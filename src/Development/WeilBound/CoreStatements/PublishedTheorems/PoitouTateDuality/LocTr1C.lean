module

public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsData
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond
public import GroundTheory.ProfiniteCohomology.PoitouTate.PtCompactDualMapEqZeroOfPtCompactToGlobalEqZero
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalInv
public import GroundTheory.ProfiniteCohomology.CupProducts.Pairing
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp
public import GroundTheory.ProfiniteCohomology.CupProducts.Graded
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
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.TransferCupDegreeZeroTwo

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.RestrictionSquareDegreeOne

section

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

theorem cupPairing_swap_degree_one {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {A B C : Rep.{0} (ULift.{0} ℤ) Γ} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (μ : A ⊗ B ⟶ C) (x : cohomology A 1) (y : cohomology B 1) :
    cupPairing μ (rfl : 1 + 1 = 2) x y = - cupPairing ((β_ B A).hom ≫ μ) (rfl : 1 + 1 = 2) y x := by
  rw [cupPairing_apply, cupPairing_apply, cohomologyMap_comp, ConcreteCategory.comp_apply,
    cohomologyMap_braiding_cup (rfl : 1 + 1 = 2) (rfl : 1 + 1 = 2) y x]
  have h1 : ((-1 : ULift.{0} ℤ) ^ (1 * 1)) = -1 := by simp
  rw [h1, neg_one_smul, map_neg, neg_neg]

attribute [local instance 2000] Rep.hV2

theorem transfer_cup_degree_one_one {Lv Hv : Type} [Group Lv] [TopologicalSpace Lv] [IsTopologicalGroup Lv]
    [Group Hv] [TopologicalSpace Hv] [IsTopologicalGroup Hv] (ev : Hv ≃* Lv)
    (hevc : Continuous ev.toMonoidHom) {R : Type} [CommRing R] {M M' P : Type}
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
    [AddCommGroup P] [Module R P] [TopologicalSpace P] [DiscreteTopology P]
    (rho : Representation R Lv M) (rho' : Representation R Lv M') (rhoP : Representation R Lv P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y)) (hc : ContAction rho')
    (A B C : Rep.{0} (ULift.{0} ℤ) Hv) [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (eA : M ≃+ A.V) (eB : M' ≃+ B.V)
    (heA : ∀ σ m, eA (rho (ev σ) m) = A.ρ σ (eA m))
    (heB : ∀ σ m, eB (rho' (ev σ) m) = B.ρ σ (eB m))
    (μ : A ⊗ B ⟶ C) (rel : P → C.V → Prop)
    (hbμ : ∀ x y, rel (b x y) (μ.hom (eA x ⊗ₜ[ULift.{0} ℤ] eB y)))
    (E : H1 rho ≃+ cohomology A 1)
    (hE : ∀ (z : ↥(Z1 rho)) (x : cocycles A 1),
      (∀ s, cochainOf A (cocycleι A 1 x) s = eA (z.1 (ev (s 0)))) →
        E (Submodule.Quotient.mk z) = cohomologyπ A 1 x)
    (E' : H1 rho' ≃+ cohomology B 1)
    (hE' : ∀ (z : ↥(Z1 rho')) (x : cocycles B 1),
      (∀ s, cochainOf B (cocycleι B 1 x) s = eB (z.1 (ev (s 0)))) →
        E' (Submodule.Quotient.mk z) = cohomologyπ B 1 x)
    {Q : Type} [AddCommGroup Q] (jp : H2 rhoP →+ Q) (J : cohomology C 2 →+ Q)
    (hJ : ∀ (W : ↥(Z2 rhoP)) (x : cocycles C 2),
      (∀ s, rel (W.1 (ev (s 0), ev (s 1))) (cochainOf C (cocycleι C 2 x) s)) →
        jp (Submodule.Quotient.mk W) = - J (cohomologyπ C 2 x))
    (z : ↥(Z1 rho)) (z' : ↥(Z1 rho')) :
    jp (cupProductH1H1 rho rho' rhoP b hb hbe hc (Submodule.Quotient.mk z) (Submodule.Quotient.mk z')) =
      - J (cupPairing μ (rfl : 1 + 1 = 2) (E (Submodule.Quotient.mk z)) (E' (Submodule.Quotient.mk z'))) := by
  obtain ⟨e1, he1a, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 Hv R M (rho.comp ev.toMonoidHom) A eA heA
  obtain ⟨x, hx⟩ := he1a (restrictCocycles1 rho ev.toMonoidHom hevc z)
  obtain ⟨e1', he1b, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 Hv R M' (rho'.comp ev.toMonoidHom) B eB heB
  obtain ⟨x', hx'⟩ := he1b (restrictCocycles1 rho' ev.toMonoidHom hevc z')
  have hEa : E (Submodule.Quotient.mk z) = cohomologyπ A 1 x := hE z x (fun s => hx s)
  have hEb : E' (Submodule.Quotient.mk z') = cohomologyπ B 1 x' := hE' z' x' (fun s => hx' s)
  have hcup : cupProductH1H1 rho rho' rhoP b hb hbe hc (Submodule.Quotient.mk z) (Submodule.Quotient.mk z') =
      Submodule.Quotient.mk (cupCocycleZ1Z1 rho rho' rhoP b hb hbe hc z z') := rfl
  rw [hEa, hEb, cupPairing_cohomologyπ, hcup]
  refine hJ _ _ (fun s => ?_)
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hx, hx']
  have h1 : Fin.partialProd s ⟨1, by omega⟩ = s 0 := by
    show Fin.partialProd s (Fin.succ 0) = s 0
    rw [Fin.partialProd_succ]
    show Fin.partialProd s 0 * s 0 = s 0
    rw [Fin.partialProd_zero, one_mul]
  rw [h1]
  have := hbμ (z.1 (ev (s 0))) (rho' (ev (s 0)) (z'.1 (ev (s 1))))
  rw [heB] at this
  exact this

theorem transfer_cup_one_one_general {Lv Hv : Type} [Group Lv] [TopologicalSpace Lv] [IsTopologicalGroup Lv]
    [Group Hv] [TopologicalSpace Hv] [IsTopologicalGroup Hv] [CompactSpace Hv]
    [TotallyDisconnectedSpace Hv] (ev : Hv ≃* Lv)
    (hevc : Continuous ev.toMonoidHom) {R : Type} [CommRing R] {M M' P : Type}
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
    [AddCommGroup P] [Module R P] [TopologicalSpace P] [DiscreteTopology P]
    (rho : Representation R Lv M) (rho' : Representation R Lv M') (rhoP : Representation R Lv P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y)) (hc : ContAction rho')
    (A B C : Rep.{0} (ULift.{0} ℤ) Hv) [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (eA : M ≃+ A.V) (eB : M' ≃+ B.V)
    (heA : ∀ σ m, eA (rho (ev σ) m) = A.ρ σ (eA m))
    (heB : ∀ σ m, eB (rho' (ev σ) m) = B.ρ σ (eB m))
    (μ' : B ⊗ A ⟶ C) (rel : P → C.V → Prop)
    (hbμ : ∀ y x, rel (b x y) (μ'.hom (eB y ⊗ₜ[ULift.{0} ℤ] eA x)))
    (E : H1 rho ≃+ cohomology A 1)
    (hE : ∀ (z : ↥(Z1 rho)) (x : cocycles A 1),
      (∀ s, cochainOf A (cocycleι A 1 x) s = eA (z.1 (ev (s 0)))) →
        E (Submodule.Quotient.mk z) = cohomologyπ A 1 x)
    (E' : H1 rho' ≃+ cohomology B 1)
    (hE' : ∀ (z : ↥(Z1 rho')) (x : cocycles B 1),
      (∀ s, cochainOf B (cocycleι B 1 x) s = eB (z.1 (ev (s 0)))) →
        E' (Submodule.Quotient.mk z) = cohomologyπ B 1 x)
    {Q : Type} [AddCommGroup Q] (jp : H2 rhoP →+ Q) (J : cohomology C 2 →+ Q)
    (hJ : ∀ (W : ↥(Z2 rhoP)) (x : cocycles C 2),
      (∀ s, rel (W.1 (ev (s 0), ev (s 1))) (cochainOf C (cocycleι C 2 x) s)) →
        jp (Submodule.Quotient.mk W) = - J (cohomologyπ C 2 x))
    (a : H1 rho') (b' : H1 rho) :
    jp (cupProductH1H1 rho rho' rhoP b hb hbe hc b' a) = J (cupPairing μ' (rfl : 1 + 1 = 2) (E' a) (E b')) := by
  induction a using Submodule.Quotient.induction_on with
  | H z' => ?_
  induction b' using Submodule.Quotient.induction_on with
  | H z => ?_
  have hbμ' : ∀ x y, rel (b x y) (((β_ A B).hom ≫ μ').hom (eA x ⊗ₜ[ULift.{0} ℤ] eB y)) :=
    fun x y => hbμ y x
  rw [cupPairing_swap_degree_one μ', map_neg,
    transfer_cup_degree_one_one ev hevc rho rho' rhoP b hb hbe hc A B C eA eB heA heB ((β_ A B).hom ≫ μ') rel hbμ'
      E hE E' hE' jp J hJ z z']

end PositivityTheory.Lit1.PTN
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.LocTr1C

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh
  GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2



theorem locTr1_C (Kf : FiniteSubfield) [NumberField Kf.1]
    [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ}
    [Fact l.Prime] (hr : 0 < r) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (inv : InvFam Kf.1 (AlgebraicClosure ℚ) l r) (hinv : PositivityTheory.PoitouTateConclusion.InvNormalised ζ inv)
    (hS : ContainsAbove S l) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (hAv : ∀ v, IsPlaceOver (Av v) v.1)
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod Kf.1 (AlgebraicClosure ℚ) l r)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (hρ : ContAction ρ) (d : FoundData Kf S l r ζ Av μ M ρ) [IsDiscreteRep d.A] [Finite d.A] (v : S)
    [IsDiscreteRep (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom
      (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A))]
    (E : H1 (ρ.comp (locFam S Av v)) ≃+ cohomology (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) 1)
    (hE : ∀ (z : ↥(Z1 (ρ.comp (locFam S Av v)))) (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) 1),
      (∀ s, cochainOf _ (cocycleι _ 1 x) s = d.eM (z.1 (d.ev v (s 0)))) → E (Submodule.Quotient.mk z) = cohomologyπ _ 1 x)
    (E' : H1 ((twDual μ ρ).comp (locFam S Av v)) ≃+ cohomology (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) 1)
    (hE' : ∀ (z : ↥(Z1 ((twDual μ ρ).comp (locFam S Av v)))) (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) 1),
      (∀ s, cochainOf _ (cocycleι _ 1 x) s = d.eD (z.1 (d.ev v (s 0)))) → E' (Submodule.Quotient.mk z) = cohomologyπ _ 1 x)
    (a : H1 (ρ.comp (locFam S Av v))) (b : H1 ((twDual μ ρ).comp (locFam S Av v))) :
    zmodToQZ (l ^ r) (invAt S Av μ hμ inv v (cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v)) b a)) =
      gsLocalInvRootsQZ (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs (l ^ r) ⟨v.1, Finset.mem_coe.2 v.2⟩ (cupPairing (ptLocalEval (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs) (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A ⟨v.1, Finset.mem_coe.2 v.2⟩) (rfl : 1 + 1 = 2) (E a) (E' b)) := by
  classical
  let places : Set (HeightOneSpectrum (𝓞 Kf.1)) := S
  let place : places := ⟨v.1, Finset.mem_coe.2 v.2⟩
  let family := gsFinFamily places d.ιs
  let localHom := (family place).toMonoidHom
  let roots := gsRoots places (l ^ r)
  let localM := Rep.res localHom d.A
  let localDual := Rep.res localHom (dualRep roots d.A)
  let localRoots := Rep.res localHom roots
  let pairing := ptLocalEval family roots d.A place
  let φ := locFam S Av v
  let ev := d.ev v
  let ρM := ρ.comp φ
  let ρD := (twDual μ ρ).comp φ
  let ρchar := (charRep μ).comp φ
  let jp := (zmodToQZ (l ^ r)).comp (invAt S Av μ hμ inv v).toAddMonoidHom
  let J := gsLocalInvRootsQZ places d.ιs (l ^ r) place
  let rel (c : ZMod (l ^ r)) (y : localRoots.V) : Prop :=
    let root : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) places) :=
      Additive.toMul y
    root.val.val.val = ζ ^ c.val
  have hc1 : Continuous ev.toMonoidHom := (d.hev_cont v).1
  have heM := hloc2 ρ φ ev (fun g => d.e g) d.A d.eM d.hM localHom (d.hev v)
  have heD := hloc2 (twDual μ ρ) φ ev (fun g => d.e g)
    (dualRep roots d.A) d.eD d.hD localHom (d.hev v)
  have hbμ (x : M) (y : TDual (ZMod (l ^ r)) M) :
      rel (evalPair x y) (pairing.hom (d.eM x ⊗ₜ[ULift.{0} ℤ] d.eD y)) :=
    d.hDζ y x
  have hJ (W : Z2 ρchar) (x : cocycles localRoots 2)
      (h : ∀ s, rel (W.1 (ev (s 0), ev (s 1))) (cochainOf localRoots (cocycleι localRoots 2 x) s)) :
      jp (Submodule.Quotient.mk W) = - J (cohomologyπ localRoots 2 x) :=
    @invCmp Kf ‹_› ‹_› places inferInstance l r ‹_› hr
      (fun w hw => Finset.mem_coe.2 (hS w hw)) ζ hζ inv hinv d.ιs place (Av v) (hAv v)
      ev (d.hιs v) hc1
      (cocycles2Map ρchar (muLoc Kf.1 l r (Av v)) LinearMap.id continuous_id
        (locFam_apply_eq S Av μ hμ v) W) x h
  have hTransfer := transfer_cup_one_one_general
    (R := ZMod (l ^ r)) (M := TDual (ZMod (l ^ r)) M) (M' := M) (P := ZMod (l ^ r)) (Q := QZ)
    ev hc1 ρD ρM ρchar evalPair.flip continuous_of_discreteTopology
    (fun g y x => evalPair_equiv μ ρ (φ g) x y) (hρ.comp' (continuous_locFam S Av v))
    localDual localM localRoots d.eD d.eM heD heM pairing rel hbμ E' hE' E hE jp J hJ a b
  -- Kernel conversion avoids a costly elaborator comparison of the cohomology types.
  run_tac Lean.Elab.Tactic.withMainContext do
    let proof ← Lean.Elab.Tactic.getFVarId (Lean.mkIdent `hTransfer)
    let goal ← Lean.Elab.Tactic.getMainGoal
    let actual ← Lean.instantiateMVars (← proof.getType)
    let expected ← Lean.instantiateMVars (← goal.getType)
    let context ← Lean.instantiateLCtxMVars (← Lean.getLCtx)
    match Lean.Kernel.isDefEq (← Lean.getEnv) context actual expected with
    | .ok true => goal.assign (.fvar proof)
    | .ok false => throwError "kernel conversion failed for the transfer result"
    | .error e => throwError "{e.toMessageData (← Lean.getOptions)}"

end PositivityTheory.Lit1.PTN
end
end
end
