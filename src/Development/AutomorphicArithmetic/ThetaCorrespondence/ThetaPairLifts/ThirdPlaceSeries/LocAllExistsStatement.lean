module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerMapRep
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiOneTameGenStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsAutSpecStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NdSpecExists
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocAutHodgeTateWeightsLevelZeroDef
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocBrOfAutSpec

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting


theorem locBr_of_autSpec_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∀ (Y : LocAut X) (Cb : LocBC Y), _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup Sp.iq Y Cb → ∃ Br : LocBr Y, Br.nbr = Sp.nbr := by
  intro D cf jE A M C tup big X T Sp Y Cb hA
  refine ⟨⟨Sp.nbr, Sp.nbr_ind, Sp.self_good, ?_⟩, rfl⟩
  intro i w hw
  have hφ : ∀ x : X.nd.O i, iotaOQ X.nd Y.naut i x =
      (((Sp.nbr i w hw).toLL x : ↥(Sp.nbr i w hw).LL.1) : Loc.Om (X.nd.l i)) := by
    intro x
    show Y.naut.iotaQ i (algebraMap _ _ x) = _
    rw [hA.iotaQ i]
    exact Sp.nbr_iq i w hw x
  have hL := A.wd.loc (X.nd.l i) (Y.naut.iotaQC i) w hw (X.nd.O i) (Sp.nbr i w hw) (Sp.nbr_ind i w hw)
    (iotaOQ X.nd Y.naut i) hφ
  refine ⟨hφ, ?_, ?_⟩
  · intro m ρ hρ
    obtain ⟨h1, h2, h3, h4⟩ := hL.1 m ρ hρ
    obtain ⟨-, e1, e2, e3, e4⟩ := hA.wdOf i m (mapRep (iotaOQ X.nd Y.naut i) ρ) w
    refine ⟨e1.trans h1, e3.trans h2, e2.trans h3, ?_⟩
    intro τ τ' hτ
    rw [show Y.naut.jumpsW i (mapRep (iotaOQ X.nd Y.naut i) ρ) τ = _ from e4 τ]
    exact h4 τ τ' hτ
  · intro LL' hLL m ρ hρ
    obtain ⟨h1, h2, h3, h4⟩ := hL.2 LL' hLL m ρ hρ
    obtain ⟨-, e1, e2, e3, e4⟩ := hA.wdOf i m (mapRep (algebraMap ↥LL'.1 (Qbar (X.nd.l i))) ρ) w
    refine ⟨e1.trans h1, e3.trans h2, e2.trans h3, ?_⟩
    intro τ τ' hτ
    rw [show Y.naut.jumpsW i (mapRep (algebraMap ↥LL'.1 (Qbar (X.nd.l i))) ρ) τ = _ from e4 τ]
    exact h4 τ τ' hτ
end GlobalTheory.HeightCounting
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NdSpecExistsStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.side_rational_eigen_data_alt : GlobalTheory.Published.GlobalArtinReciprocity → HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → ∀ big : D.what₂.places.Pl → Finset ℂ, ∃ (X : LocNd (lay0 D)) (T : LocTw X), Nonempty (NdSpec A.pl M C big X T) := by
  first | exact @_root_.GlobalTheory.HeckeLocN.ndSpec_exists_alt | exact _root_.GlobalTheory.HeckeLocN.ndSpec_exists_alt | (intros; apply _root_.GlobalTheory.HeckeLocN.ndSpec_exists_alt <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeVISupIndep

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.MtIndep

section rep
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem isoRep_trans {W₁ W₂ W₃ : Type} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
    [AddCommGroup W₃] [Module ℂ W₃] {S₁ : Submodule ℂ (GAf L n → W₁)} {S₂ : Submodule ℂ (GAf L n → W₂)}
    {S₃ : Submodule ℂ (GAf L n → W₃)} (h₁ : NG.IsoRep S₁ S₂) (h₂ : NG.IsoRep S₂ S₃) : NG.IsoRep S₁ S₃ := by
  obtain ⟨T, hT⟩ := h₁
  obtain ⟨U, hU⟩ := h₂
  exact ⟨T.trans U, fun h f f' e => hU h (T f) (T f') (hT h f f' e)⟩

theorem isoRep_symm {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ (GQ L n) W} {S₁ : Submodule ℂ (GAf L n → W)} {S₂ : Submodule ℂ (GAf L n → W')}
    (hs : NG.IsSubrep ρ S₁) (h : NG.IsoRep S₁ S₂) : NG.IsoRep S₂ S₁ := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.symm, fun h g g' e => ?_⟩
  have hm : NG.rt L n h ((T.symm g : S₁) : GAf L n → W) ∈ S₁ := hs.stable h _ (T.symm g).2
  have key := hT h (T.symm g) ⟨_, hm⟩ rfl
  rw [LinearEquiv.apply_symm_apply] at key
  have hg : T ⟨_, hm⟩ = g' := Subtype.ext (key.trans e.symm)
  rw [← hg, LinearEquiv.symm_apply_apply]

theorem isoTyp_eq {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (GQ L n) W}
    {S₁ S₂ : Submodule ℂ (GAf L n → W)} (hs : NG.IsSubrep ρ S₁) (h : NG.IsoRep S₁ S₂) :
    NG.isoTyp ρ S₁ = NG.isoTyp ρ S₂ := by
  unfold NG.isoTyp
  congr 1
  ext S'
  simp only [Set.mem_setOf_eq]
  exact and_congr_right fun _ => ⟨fun h' => isoRep_trans (isoRep_symm hs h) h', fun h' => isoRep_trans h h'⟩

end rep

section loc
variable {D : D7}

def BCd (X : LocNd (lay0 D)) (Y : LocAut X) (Pa : List (Part Y.naut.CG)) (loc : ∀ w, Y.naut.LP w)
    (sat : PlE D.host → Multiset ℂ) (inf : (D.host.E →+* ℂ) → Multiset ℂ) : Prop :=
  (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ Y.naut.csd p.π) ∧
  (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a, Y.naut.CG a), p.d)).Nodup ∧
  rankIso X.nd Y.naut Pa = D.R.nV ∧
  (∀ w, IsSplitPl D.host w → isoLoc X.nd Y.naut Pa w = loc w) ∧
  (∀ w, ¬ IsSplitPl D.host w → Y.naut.unr (isoLoc X.nd Y.naut Pa w) ∧
    Y.naut.frobEig (isoLoc X.nd Y.naut Pa w) = ubc D.R.nV (sat w)) ∧
  ∀ τ, isoInf X.nd Y.naut Pa τ = inf τ

def Good (X : LocNd (lay0 D)) (Y : LocAut X) (σ' : D.ntypes.Par) (c : Y.naut.CG 1) (j : ℕ) (u : D.nbc.AU j) : Prop :=
  ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧
    BCd X Y (twistIso X.nd Y.naut (Sig ++ [⟨1, c, D.R.t⟩]) Y.naut.etaTinv) (fun w => D.nbc.locAU j u w)
      (D.nbc.satAU j u) (D.nbc.infW j (D.nbc.wtAU j u))

end loc

end GlobalTheory.HeightCounting.MtIndep

namespace GlobalTheory.HeightCounting.MtIndep

section loc2
variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D}
  {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {X : LocNd (lay0 D)}
  {iq : ∀ i : X.nd.Loc, FractionRing (X.nd.O i) →+* Qbar (X.nd.l i)} {Y : LocAut X} {Cb : LocBC Y}

end loc2

end GlobalTheory.HeightCounting.MtIndep
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeVISupIndep

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting.MtIndep
section rep
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end rep
section loc
variable {D : D7}
def phiSubmodule {cf : CharFrame D} {jE : D.host.E →+* Qb} (X : LocNd (lay0 D)) (Y : LocAut X) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D)
    (σ' : D.ntypes.Par) (c : Y.naut.CG 1) (μ : D.what₂.Tup) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    Submodule ℂ (D.what₂.Mt μ j) :=
  ⨆ (S' : Submodule ℂ (GAf D.host.E D.R.nV → (M μ j h1 h2).wt.W)) (h : NG.IsIrrRep (M μ j h1 h2).wt.ρ S')
    (_ : Good X Y σ' c j (A.au.cls j h1 h2 { (M μ j h1 h2).wt with S := S', irrS := h })),
    (NG.isoTyp (M μ j h1 h2).wt.ρ S').comap (M μ j h1 h2).real
theorem phi_submodule_heq {cf : CharFrame D} {jE : D.host.E →+* Qb} (X : LocNd (lay0 D)) (Y : LocAut X) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE)
    (M : MtFam D) (σ' : D.ntypes.Par) (c : Y.naut.CG 1) {μ μ' : D.what₂.Tup} {j j' : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (h1' : 1 ≤ j') (h2' : j' ≤ D.R.m) (hμ : μ = μ') (hj : j = j') :
    HEq (_root_.GlobalTheory.HeightCounting.MtIndep.phiSubmodule X Y A M σ' c μ j h1 h2) (_root_.GlobalTheory.HeightCounting.MtIndep.phiSubmodule X Y A M σ' c μ' j' h1' h2') := by
  subst hμ hj; rfl
end loc
end GlobalTheory.HeightCounting.MtIndep
namespace GlobalTheory.HeightCounting.MtIndep
section loc2
variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : MtFam D}
  {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {X : LocNd (lay0 D)}
  {iq : ∀ i : X.nd.Loc, FractionRing (X.nd.O i) →+* Qbar (X.nd.l i)} {Y : LocAut X} {Cb : LocBC Y}
theorem supr_type_v_eq_phi_submodule (hS : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup iq Y Cb) (σ' : D.ntypes.Par) (i : X.nd.Loc) :
    (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)}, Y.naut.typeV i P) =
    _root_.GlobalTheory.HeightCounting.MtIndep.phiSubmodule X Y A M σ' (Y.muC i) (X.nd.mu i) (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 := by
  have hc : ∀ P, (∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)) ↔
      Good X Y σ' (Y.muC i) (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2
        { (mlX M X i).wt with S := hS.S i P, irrS := hS.irr i P }) := by
    intro P
    have hl : Y.naut.locV i P = fun w => D.nbc.locAU (X.nd.j i) (Cb.embAV i P) w := funext (Cb.embAV_loc i P)
    have hs : Y.naut.satV i P = D.nbc.satAU (X.nd.j i) (Cb.embAV i P) := funext (Cb.embAV_sat i P)
    have hf : Y.naut.infWt i = D.nbc.infW (X.nd.j i) (D.nbc.wtAU (X.nd.j i) (Cb.embAV i P)) := Cb.embAV_inf i P
    rw [← hS.emb i P]
    unfold Good
    refine exists_congr fun Sig => and_congr_right fun _ => ?_
    unfold IsBCV BCd
    rw [hl, hs, hf]
    exact Iff.rfl
  apply le_antisymm
  · refine iSup₂_le fun P hP => ?_
    rw [hS.typeV i P]
    exact le_iSup_of_le (hS.S i P) (le_iSup_of_le (hS.irr i P) (le_iSup_of_le ((hc P).1 hP) le_rfl))
  · refine iSup_le fun S' => iSup_le fun hirr => iSup_le fun hg => ?_
    by_cases hb : (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real = ⊥
    · exact hb.le.trans bot_le
    · obtain ⟨P, hP⟩ := hS.surj i S' hirr hb
      have ht : Y.naut.typeV i P = (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real := by
        rw [hS.typeV i P, isoTyp_eq (hS.irr i P).1 hP]
      have hcl : A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2
            { (mlX M X i).wt with S := hS.S i P, irrS := hS.irr i P } =
          A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2
            { (mlX M X i).wt with S := S', irrS := hirr } :=
        (A.au.iso _ _ _ _ _).2 ⟨⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩, hP⟩
      have hP' : P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)} :=
        (hc P).2 (hcl ▸ hg)
      exact le_iSup₂_of_le (f := fun P _ => Y.naut.typeV i P) P hP' ht.ge
end loc2
theorem typeV_iSup_indep_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∀ (Y : LocAut X) (Cb : LocBC Y), _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq Y Cb → ∀ (i i' : X.nd.Loc) (σ' : D.ntypes.Par), X.nd.mu i = X.nd.mu i' → X.nd.j i = X.nd.j i' → HEq (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)}, Y.naut.typeV i P) (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i' P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i']) Y.naut.etaTinv)}, Y.naut.typeV i' P) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp _ _ _ _ _ _ big X T Sp Y Cb hS i i' σ' hmu hj
  rw [_root_.GlobalTheory.HeightCounting.MtIndep.supr_type_v_eq_phi_submodule hS σ' i, _root_.GlobalTheory.HeightCounting.MtIndep.supr_type_v_eq_phi_submodule hS σ' i']
  have hc : Y.muC i = Y.muC i' := by
    obtain ⟨h1, h2⟩ := X.nd.j_range i
    have e := hS.muC i ⟨X.nd.j i - 1, by omega⟩ (by simp only; omega)
    have e' := hS.muC i' ⟨X.nd.j i - 1, by omega⟩ (by simp only; omega)
    rw [hmu] at e
    exact A.chr.e1.injective (Subtype.ext (e.trans e'.symm))
  rw [hc]
  exact _root_.GlobalTheory.HeightCounting.MtIndep.phi_submodule_heq X Y A M σ' _ _ _ _ _ hmu hj
end GlobalTheory.HeightCounting.MtIndep
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocAllExists

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting

theorem locAll_exists_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → (Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) → BlocksUnique D → ∀ big : D.what₂.places.Pl → Finset ℂ, ∃ (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T), Nonempty (_root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C) ∧ ∀ σ lam, IsSSRep (L.Z.rbar σ lam) := by
  intro hGAR D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb hpsi hO hBU big
  obtain ⟨X, T, ⟨Sp⟩⟩ := _root_.GlobalTheory.T.side_rational_eigen_data_alt hGAR GlobalTheory.HeckeStdFacts.heckeStdPlain D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb hO hpsi big
  obtain ⟨Y, Cb, ⟨aut⟩⟩ := _root_.GlobalTheory.T.side_rational_level_data_alt hGAR D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb hpsi big X T Sp
  obtain ⟨Br, -⟩ := _root_.GlobalTheory.HeightCounting.locBr_of_autSpec_alt D cf jE A M C tp.tup big X T Sp Y Cb aut
  have hchi := _root_.GlobalTheory.T.side_rational_character_data_alt hGAR D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb big X T Sp Y Cb aut
  have hMt := _root_.GlobalTheory.HeightCounting.MtIndep.typeV_iSup_indep_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb big X T Sp Y Cb aut
  obtain ⟨Z, hbc, hrb, hmt, hss⟩ := locTy_exists D A.row A.pl X Y hBU hCheb aut.locW aut.iotaQC aut.kFbar Sp.heckeLoc_gamma_places hchi hMt
  exact ⟨{ X := X, T := T, Y := Y, C := Cb, Z := Z, B := Br, bc_tie := hbc, rbar_tie := hrb, mtpar_tie := hmt }, Sp, ⟨aut⟩, hss⟩
end GlobalTheory.HeightCounting
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocAllExistsStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.side_rational_hecke_data_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → (Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) → BlocksUnique D → ∀ big : D.what₂.places.Pl → Finset ℂ, ∃ (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T), Nonempty (_root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C) ∧ ∀ σ lam, IsSSRep (L.Z.rbar σ lam) := by
  first | exact @_root_.GlobalTheory.HeightCounting.locAll_exists_alt | exact _root_.GlobalTheory.HeightCounting.locAll_exists_alt | (intros; apply _root_.GlobalTheory.HeightCounting.locAll_exists_alt <;> assumption)
end
end
end
