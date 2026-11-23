module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.StFull
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LPermSub
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LRCuspCsd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LRSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfInvT
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfIsCompAlongSplit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.SplitSph
import Mathlib.Tactic.Linter.Style
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LStrSat
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LWeightEx
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.ThetaOfCsdR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetOfStringsDeterminesPointsDegreesStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.ResidualRigidity.AllPlaceRigidityResidual
public import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.AscSeedHolds2

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LInertSatExb

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB.F.Rig.B

theorem inertSatEx : InertSatEx := by
  intro E _ _ _ hE n π hπ w hw hu
  exact GlobalTheory.BcSpehCompare.exists_hasSatAt (fun v => hE v) hπ hw hu

end PositivityTheory.Rg.BcB.F.Rig.B

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LRFull

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.One

namespace PositivityTheory.Rg.BcB.F.Rig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem rfull_finite_under_eq (u : HeightOneSpectrum (𝓞 E)) :
    {w : HeightOneSpectrum (𝓞 E) |
      w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E))}.Finite := by
  have hm : (u.under (𝓞 (maximalRealSubfield E))).asIdeal.IsMaximal := (u.under _).isMaximal
  refine (Set.Finite.preimage (f := HeightOneSpectrum.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)
    (IsDedekindDomain.primesOver_finite (u.under (𝓞 (maximalRealSubfield E))).asIdeal (𝓞 E))).subset ?_
  intro w hw
  exact ⟨w.isPrime, ⟨by rw [← hw]; rfl⟩⟩

theorem rfull_eventually_sat (D : Pre E n) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, D.Sat w B := by
  have h : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      ∀ i, GlobalTheory.LGrp.IsSpherical (D.σ i w).ρ (GlobalTheory.LFun.KGL w (n := (D.N i))) :=
    Filter.eventually_all.2 fun i =>
      (GlobalTheory.SpehPair.eventually_spherical (D.discrete i)).mono fun w hw => hw _ (D.loc i w)
  refine h.mono fun w hw => ?_
  choose b hb using fun i =>
    GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible (D.σ i w).smooth (D.σ i w).irred (hw i)
  exact ⟨∑ i, b i, b, fun i => ⟨hw i, hb i⟩, rfl⟩

theorem rfull_bcParam_map_inv (n : ℕ) (α : Fin (n / 2) → ℂˣ) :
    (GlobalTheory.LGrp.bcParam n α).map (·⁻¹) = GlobalTheory.LGrp.bcParam n α := by
  simp only [GlobalTheory.LGrp.bcParam, Multiset.map_add (f := _), Multiset.map_map, Function.comp_def, inv_inv,
    Multiset.map_replicate, inv_one]
  rw [add_comm (Multiset.map _ _) (Multiset.map _ _)]

theorem rFullSat : RFullSat := by
  intro hU hI hS E _ _ _ hE n π hπ D D' hD hD'
  filter_upwards [hU E n π hπ, hS E n π hπ D D' hD.1.2 hD'.1.2] with w hu hsp
  by_cases hw : IsSplitAt w
  · exact hsp hw
  · obtain ⟨s, ϖ, q, α, hs, hinv, hα⟩ := hI E hE n π hπ w hw hu
    obtain ⟨B, hB, hBα⟩ := hD.2 w hu hw
    obtain ⟨B', hB', hBα'⟩ := hD'.2 w hu hw
    refine ⟨B, hB, ?_⟩
    rw [hBα s ϖ q hs hinv α hα, ← hBα' s ϖ q hs hinv α hα]
    exact hB'

theorem rFullTheta : RFullTheta := by
  intro hU hI hC E _ _ _ hE n π hπ D hD
  have hbad : {u : HeightOneSpectrum (𝓞 E) |
      ¬ ((∃ B, D.Sat u B) ∧ (IsSplitAt u → D.SplitAt π u))}.Finite := by
    refine ((Filter.eventually_cofinite.1 (rfull_eventually_sat D)).union hD.1.2).subset ?_
    intro u hu
    by_cases h1 : ∃ B, D.Sat u B
    · right
      by_contra h2
      exact hu ⟨h1, fun hs => by_contra fun h3 => h2 ⟨hs, h3⟩⟩
    · left
      exact h1
  have hconj : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ u, ConjPl w u →
      (∃ B, D.Sat u B) ∧ (IsSplitAt u → D.SplitAt π u) := by
    rw [Filter.eventually_cofinite]
    refine (hbad.biUnion fun u _ => rfull_finite_under_eq u).subset ?_
    intro w hw
    have hw' : ¬ ∀ u, ConjPl w u → (∃ B, D.Sat u B) ∧ (IsSplitAt u → D.SplitAt π u) := hw
    obtain ⟨u, hu⟩ := not_forall.1 hw'
    obtain ⟨hc, hu'⟩ := Classical.not_imp.1 hu
    exact Set.mem_biUnion hu' hc.1.symm
  have hsp0 : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ¬ (IsSplitAt w ∧ ¬ D.SplitAt π w) :=
    Filter.eventually_cofinite.2 (hD.1.2.subset fun x hx => not_not.1 hx)
  filter_upwards [hU E n π hπ, rfull_eventually_sat D, hconj, hsp0]
    with w hu hs hc hsp
  by_cases hw : IsSplitAt w
  · obtain ⟨B, hB⟩ := hs
    refine ⟨B, hB, fun u hwu => ?_⟩
    obtain ⟨⟨B', hB'⟩, hsu⟩ := hc u hwu
    have hus : IsSplitAt u := ⟨w, (hwu.2.resolve_right (not_not_intro hw)).symm, hwu.1.symm⟩
    have hsw : D.SplitAt π w := by
      by_contra h
      exact hsp ⟨hw, h⟩
    have e := hC E n π hπ D w u hw hwu hu hsw (hsu hus) B B' hB hB'
    rw [← e]
    exact hB'
  · obtain ⟨s, ϖ, q, α, hs', hinv, hα⟩ := hI E hE n π hπ w hw hu
    obtain ⟨B, hB, hBα⟩ := hD.2 w hu hw
    refine ⟨B, hB, fun u hwu => ?_⟩
    have hu' : u = w := by
      by_contra hne
      exact hw ⟨u, hne, hwu.1⟩
    subst hu'
    have e := hBα s ϖ q hs' hinv α hα
    rw [e, rfull_bcParam_map_inv, ← e]
    exact hB

end PositivityTheory.Rg.BcB.F.Rig

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LSplitConj

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig

open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}


omit [IsCMField E] in
theorem sc_hasSatGL_of_isSubquotient {w : HeightOneSpectrum (𝓞 E)} {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (hρs : IsSmooth ρ)
    (σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W) (hsub : GlobalTheory.SmGL.IsSubquotient σ ρ)
    (hsph : GlobalTheory.LGrp.IsSpherical σ (GlobalTheory.LFun.KGL w (n := n))) (B : Multiset ℂˣ)
    (hsat : ∀ f ∈ fixed ρ (GlobalTheory.LFun.KGL w (n := n)), f ≠ 0 → GlobalTheory.LFun.IsSatVecGL w ρ f B) :
    GlobalTheory.LFun.HasSatGL w σ B := by
  obtain ⟨S, q, hq⟩ := hsub
  obtain ⟨-, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  have hSs : IsSmooth S.toRepresentation := fun y => by
    refine (congrArg IsOpen ?_).mpr (hρs y.1)
    ext g
    exact Subtype.ext_iff
  refine ⟨hsph, fun x hx hx0 => ?_⟩
  have hx' : x ∈ (fixed S.toRepresentation (GlobalTheory.LFun.KGL w (n := n))).map q.toLinearMap := by
    rw [GlobalTheory.LocGL.map_fixed_of_surjective hSs hKc (f := q) hq]
    exact hx
  obtain ⟨u, hu, hux⟩ := Submodule.mem_map.1 hx'
  have hu0 : u ≠ 0 := fun e => hx0 (by rw [← hux, e, map_zero])
  have huK : u.1 ∈ fixed ρ (GlobalTheory.LFun.KGL w (n := n)) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hu k hk)
  have hu1 : GlobalTheory.LFun.IsSatVecGL w ρ u.1 B := hsat _ huK fun e => hu0 (Subtype.ext e)
  have hu2 : GlobalTheory.LFun.IsSatVecGL w S.toRepresentation u B :=
    GlobalTheory.LFun.IsSatVecGL.of_map (ρ' := ρ) S.toSubmodule.subtype (fun _ _ => rfl) Subtype.val_injective hu1
  have hu3 : GlobalTheory.LFun.IsSatVecGL w σ (q.toLinearMap u) B :=
    hu2.map (ρ' := σ) q.toLinearMap (fun g y => Representation.IntertwiningMap.isIntertwining _ _ q g y)
      (by rw [hux]; exact hx0)
  rw [hux] at hu3
  exact hu3

theorem sc_satVec (X : Pre E n) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) (h : X.Sat w B) :
    ∀ f ∈ fixed (locProd X.h w (X.σ · w)) (GlobalTheory.LFun.KGL w (n := n)), f ≠ 0 →
      GlobalTheory.LFun.IsSatVecGL w (locProd X.h w (X.σ · w)) f B := by
  obtain ⟨b, hb, rfl⟩ := h
  intro f hf hf0
  obtain ⟨S, hS, hfS⟩ := GlobalTheory.SatInd.exists_sat_multiProd X.h (π := fun i => (X.σ i w).ρ)
    (fun i => (X.σ i w).smooth) (fun i => (X.σ i w).irred) hf hf0
  have e : S = b := funext fun a => (hS a).unique (hb a).2
  rw [← e]
  exact hfS

theorem sc_cLoc_conj (x : UA E n) (u : HeightOneSpectrum (𝓞 E)) :
    cLoc u x = GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc u) n (cLoc (GlobalTheory.ThetaSatake.cw u) x) := by
  have h : ((GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv u)
      (cLoc (GlobalTheory.ThetaSatake.cw u) x)).val)ᵀ * (cLoc u x).val = 1 := GlobalTheory.SplitPts.comp_eq x u
  generalize hM : GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv u)
      (cLoc (GlobalTheory.ThetaSatake.cw u) x) = M at h
  have h1 : ((M⁻¹ : GL (Fin n) (u.adicCompletion E)).val)ᵀ * (M.val)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have h2 : (cLoc u x).val = ((M⁻¹ : GL (Fin n) (u.adicCompletion E)).val)ᵀ := by
    calc (cLoc u x).val = ((M⁻¹ : GL (Fin n) (u.adicCompletion E)).val)ᵀ * ((M.val)ᵀ * (cLoc u x).val) := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
      _ = _ := by rw [h, Matrix.mul_one]
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [h2, GlobalTheory.LFun.ConjPlace.invT_val, Matrix.transpose_apply, ← hM, ← map_inv]
  rfl

theorem splitConj : SplitConj := by
  intro E _ _ _ n π hπ D w u hw hwu hu hDw hDu B B' hB hB'
  obtain ⟨-, -, hover⟩ := GlobalTheory.SplitPts.over_split hw
  have huw : u ≠ w := hwu.2.resolve_right (not_not.2 hw)
  have hu' : u = conjSrc (GlobalTheory.SplitPts.conjE E) w := (hover u hwu.1).resolve_left huw
  have hw' : w = GlobalTheory.ThetaSatake.cw u := by
    rw [hu']
    exact (GlobalTheory.SplitPts.conjSrc_conjSrc_cm w).symm
  clear hu' hover
  subst hw'
  obtain ⟨P, hPsub, hPc⟩ := hDw
  obtain ⟨P', hP'sub, hP'c⟩ := hDu
  have hPsat : GlobalTheory.LFun.HasSatGL (GlobalTheory.ThetaSatake.cw u) P.ρ B :=
    sc_hasSatGL_of_isSubquotient (locProd D.h _ (D.σ · _)) (GlobalTheory.SmGL.isSmooth_parInd _ _) P.ρ hPsub
      (GlobalTheory.PfBCI.split_spherical hπ hw P hPc hu) B (sc_satVec D _ B hB)
  have hq : Formalism.UG.qV E u = Formalism.UG.qV E (GlobalTheory.ThetaSatake.cw u) := (GlobalTheory.ThetaSatake.absNorm_cw u).symm
  have hQsat : GlobalTheory.LFun.HasSatGL u
      (P.ρ.comp (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc u) n).symm.toMonoidHom) (B.map (·⁻¹)) :=
    GlobalTheory.ThetaSatake.hasSatGL_of_invT (GlobalTheory.ThetaSatake.cloc u) (conjLoc_spec _ u).2.2 hq (LinearEquiv.refl ℂ P.V)
      (fun g x => by
        show P.ρ ((GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc u) n).symm
          (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc u) n g)) x = P.ρ g x
        rw [MulEquiv.symm_apply_apply]) hPsat
  have hloc : locU n u = locU n (GlobalTheory.ThetaSatake.cw u) := by
    simp only [locU, hwu.1]
  have hQc : IsCompAlong π (locU n u) ((cLoc u).comp (locU n u).subtype)
      (P.ρ.comp (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc u) n).symm.toMonoidHom) := by
    obtain ⟨hirr, f, hf0, hfm, hf⟩ := hPc
    refine ⟨GlobalTheory.PfBCI.SplitSph.isIrreducible_comp_surj P.ρ _
      (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc u) n).symm.surjective hirr, f, hf0, hfm, fun x v => ?_⟩
    have hx : (x : UA E n) ∈ locU n (GlobalTheory.ThetaSatake.cw u) := hloc ▸ x.2
    have e := hf ⟨x, hx⟩ v
    show f (P.ρ ((GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc u) n).symm (cLoc u (x : UA E n))) v) =
      RU E n (x : UA E n) (f v)
    rw [sc_cLoc_conj (x : UA E n) u, MulEquiv.symm_apply_apply]
    exact e
  have hsu : IsSplitAt u := ⟨GlobalTheory.ThetaSatake.cw u, Ne.symm huw, hwu.1.symm⟩
  have hP'inv : GlobalTheory.LFun.HasSatGL u P'.ρ (B.map (·⁻¹)) :=
    GlobalTheory.SplitSatake.hasSatGL_of_isCompAlong_split E n π hπ u hsu _ _ _ P'.ρ hQc hP'c _ hQsat
  have hP'B' : GlobalTheory.LFun.HasSatGL u P'.ρ B' :=
    sc_hasSatGL_of_isSubquotient (locProd D.h u (D.σ · u)) (GlobalTheory.SmGL.isSmooth_parInd _ _) P'.ρ hP'sub hP'inv.1 B'
      (sc_satVec D u B' hB')
  exact hP'B'.unique hP'inv

end PositivityTheory.Rg.BcB.F.Rig

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.OfEqOfIsSpeh

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem of_eq_of_isSpeh {w : HeightOneSpectrum (𝓞 E)} {N N' : ℕ} (σ : SmIrr (GL (Fin N) (w.adicCompletion E)))
    (σ' : SmIrr (GL (Fin N') (w.adicCompletion E))) (x : GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E)) (d : ℕ)
    (h : GlobalTheory.LocGL.IsSpeh x d σ.ρ) (h' : GlobalTheory.LocGL.IsSpeh x d σ'.ρ) :
    GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred = GlobalTheory.LocGL.IrrGL.of σ'.ρ σ'.smooth σ'.irred := by
  obtain ⟨hd, hc⟩ := h
  obtain ⟨hd', hc'⟩ := h'
  obtain rfl : N = N' := hd.symm.trans hd'
  exact GlobalTheory.LocGL.IrrGL.of_eq_of.2 (GlobalTheory.LocGL.IsCosocle.unique hc' hc)

theorem ascEmb_of_sigma {N a a' d : ℕ} {V : Submodule ℂ (Sm E N)} (P : CuspSub E a) (P' : CuspSub E a')
    (h : ∀ P'' : CuspSub E a', P'.Iso P'' → AscEmb V P'' d)
    (e : (⟨a', CG.mk P'⟩ : Σ b, CG E b) = ⟨a, CG.mk P⟩) : AscEmb V P d := by
  obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.mp e
  exact h P (Quotient.exact (eq_of_heq he))

theorem rLoc : RLoc := by
  intro hJS hSS hStr E _ _ _ n D D' hr hr' hsat
  choose a d P ha hd hPu hPn hPs using hStr E n D hr
  choose a' d' P' ha' hd' hPu' hPn' hPs' using hStr E n D' hr'
  have he : ∀ i, AscEmb (D.V i) (P i) (d i) := fun i => hPs i (P i) (Setoid.refl (α := CuspSub E (a i)) (P i))
  have he' : ∀ j, AscEmb (D'.V j) (P' j) (d' j) := fun j =>
    hPs' j (P' j) (Setoid.refl (α := CuspSub E (a' j)) (P' j))
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E
  have h1 := Filter.eventually_all.2 fun i => hSS E (D.N i) (a i) (d i) (D.V i) (P i) (D.σ i) (D.pos i)
    (D.discrete i) (hPu i) (hPn i) (he i) (D.loc i) (fun k => GlobalTheory.HeckeGal.Model.absPow E (spehExp (d i) k))
    (fun k => hν _)
  have h2 := Filter.eventually_all.2 fun j => hSS E (D'.N j) (a' j) (d' j) (D'.V j) (P' j) (D'.σ j) (D'.pos j)
    (D'.discrete j) (hPu' j) (hPn' j) (he' j) (D'.loc j) (fun k => GlobalTheory.HeckeGal.Model.absPow E (spehExp (d' j) k))
    (fun k => hν _)
  obtain ⟨s, hs⟩ := GlobalTheory.Published.JacquetShalikaRigidity.unitary hJS (ι := Σ i, Fin (d i)) (κ := Σ j, Fin (d' j))
    (fun x => CG.mk (P x.1)) (fun y => CG.mk (P' y.1)) (fun x => ha x.1) (fun y => ha' y.1)
    (fun x => (CG.isUnitary_mk _).2 (hPu x.1)) (fun y => (CG.isUnitary_mk _).2 (hPu' y.1)) _ hν
    (fun x => spehExp (d x.1) x.2) (fun y => spehExp (d' y.1) y.2) (by
      filter_upwards [h1, h2, hsat] with w hw hw' hB
      obtain ⟨B, ⟨b, hb, hbB⟩, ⟨b', hb', hbB'⟩⟩ := hB
      choose c hc hsph hcs using hw
      choose c' hc' hsph' hcs' using hw'
      refine ⟨fun x => c x.1 x.2, fun y => c' y.1 y.2, fun x => hc x.1 x.2, fun y => hc' y.1 y.2, ?_⟩
      rw [Fintype.sum_sigma, Fintype.sum_sigma]
      have e1 : ∀ i, ∑ k, c i k = b i := fun i => (hcs i).unique (hb i).2
      have e2 : ∀ j, ∑ k, c' j k = b' j := fun j => (hcs' j).unique (hb' j).2
      simp only [e1, e2]
      exact hbB.trans hbB'.symm)
  have hstr := GlobalTheory.Rigid.strings_eq_of_equiv (fun i => (⟨a i, CG.mk (P i)⟩ : Σ b, CG E b)) d
    (fun j => (⟨a' j, CG.mk (P' j)⟩ : Σ b, CG E b)) d' s fun x => ⟨(hs x).1, (hs x).2⟩
  obtain ⟨s0, hs0⟩ := GlobalTheory.T.multiset_of_strings_determines_points_degrees _ d _ d' hd hd' hstr
  refine ⟨s0, fun i w => ?_⟩
  have hA : AscEmb (D'.V (s0 i)) (P i) (d i) := by
    rw [(hs0 i).2]
    exact ascEmb_of_sigma (P i) (P' (s0 i)) (hPs' (s0 i)) (hs0 i).1.symm
  obtain ⟨σ0, hσ0, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp CuspFormAutomorphicBounds.automorphicFormsFiniteGL E (a i) (P i) w
  have k1 := ascSeed_holds2.2 E (D.N i) (a i) (d i) (D.V i) (P i) (D.pos i) (D.discrete i) (hPu i) (hPn i) (he i)
    w σ0 (D.σ i w) hσ0 (D.loc i w)
  have k2 := ascSeed_holds2.2 E (D'.N (s0 i)) (a i) (d i) (D'.V (s0 i)) (P i) (D'.pos _) (D'.discrete _) (hPu i)
    (hPn i) hA w σ0 (D'.σ (s0 i) w) hσ0 (D'.loc _ w)
  exact of_eq_of_isSpeh _ _ _ _ k1 k2

end PositivityTheory.Rg.BcB.F.Rig

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.FullThetaHolds

section

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.Rig

open PositivityTheory.Rg.BcB.One

theorem strings_holds : Strings := rStrings regPart

theorem cuspCsd_holds : CuspCsd := rCuspCsd PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity strSat strings_holds

theorem locRigid_holds : LocRigid := rLoc PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity strSat strings_holds

theorem unrAE_holds : UnrAE := fun _ _ _ _ _ _ hπ => eventually_isUnramU hπ

theorem fullSat_holds : FullSat := rFullSat unrAE_holds B.inertSatEx splitSatPre

theorem fullTheta_holds : FullTheta := rFullTheta unrAE_holds B.inertSatEx splitConj

theorem fieldN_of_run (hR : RunFin) : PositivityTheory.Rg.BcN.BaseChangeIsobaricN :=
  fieldN_of hR fullSat_holds fullTheta_holds weightEx strings_holds cuspCsd_holds locRigid_holds permSub

end PositivityTheory.Rg.BcB.F.Rig
end
end
