module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Mathlib.NumberTheory.LocalField.Basic
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLtOneIffTendsto
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne

-- Source module: Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.SeeSawFourier

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.SeeSawLineFourier

variable {D : D7}

def nrm (L : HSp D) (ζ : Fin L.rank → D.host.E) : D.host.E := star ζ ⬝ᵥ L.gram *ᵥ ζ

def colQ {m : ℕ} (ζ : Fin m → D.host.E) : Matrix (Fin m) (Fin 1) D.host.E := replicateCol (Fin 1) ζ

def beta (S : HSp D) {L L'' : HSp D} (ζ₁ : Fin L.rank → D.host.E) (ζ : Fin L''.rank → D.host.E) (x : WO L S) : WO S L'' :=
  (rat (colQ ζ) : Mx D L''.rank 1) *
    (adj (incA D (nrm L'' ζ)⁻¹ • (x * (rat (colQ ζ₁) : Mx D L.rank 1) : Mx D S.rank 1)) * gA S : Mx D 1 S.rank)

def OppLines (L L'' : HSp D) (ζ₁ : Fin L.rank → D.host.E) (ζ : Fin L''.rank → D.host.E) : Prop :=
  IsLineVec L ζ₁ ∧ IsLineVec L'' ζ ∧ nrm L ζ₁ = -nrm L'' ζ

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def weilChar (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (a : k) : ℂ := psiE ψ (incA D D.host.xi0 * p.sec a)

variable {p : SplitPt D k} {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def atW (α : Frame p S n') (β : Frame p T n) (x : Matrix n n' k) : WO S T :=
  Matrix.map (β.b * (x * α.b') : Matrix (Fin T.rank) (Fin S.rank) k) p.sec

def IsModel (ψ : AddChar (AF D.host.F) ℂ) (α : Frame p S n') (β : Frame p T n)
    (M : (Matrix n n' k → ℂ) →ₗ[ℂ] (WO S T → ℂ)) : Prop :=
  ∀ Φ ∈ SB (Matrix n n' k), IsThetaFunO ψ S T (M Φ) ∧
    (∀ a : Matrix n n' k, M (fun x => Φ (x + a)) = heisO ψ S T (atW α β a) (M Φ)) ∧
    ∀ a' : WO S T, IsHalf (cA D p.e) a' →
      M (fun x => ψ (symplO S T (atW α β x) a') * Φ x) = heisO ψ S T a' (M Φ)

def IsLineFrame {L : HSp D} (ζ : Fin L.rank → D.host.E) (α : Frame p L (Fin 1)) : Prop :=
  α.b = replicateCol (Fin 1) fun i => p.pr (ratV ζ i)

def ofCol (f : (n → k) → ℂ) (x : Matrix n (Fin 1) k) : ℂ := f fun i => x i 0

def ofRow (g : (n → k) → ℂ) (x : Matrix (Fin 1) n k) : ℂ := g (x 0)

variable [MeasurableSpace k] [BorelSpace k]

def hat (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (ν : Measure k) (f : (n → k) → ℂ) (η : n → k) : ℂ :=
  ∫ y, f y * weilChar p ψ (-(η ⬝ᵥ y)) ∂(Measure.pi fun _ => ν)

end Local

def LineFourier (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
  ∀ (S L L'' : HSp D) (ζ₁ : Fin L.rank → D.host.E) (ζ : Fin L''.rank → D.host.E), OppLines L L'' ζ₁ ζ →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure →
  ∀ (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (b : Frame p S n) (a₁ : Frame p L (Fin 1))
    (a : Frame p L'' (Fin 1)), IsLineFrame ζ₁ a₁ → IsLineFrame ζ a →
  ∀ M₁ : (Matrix n (Fin 1) k → ℂ) →ₗ[ℂ] (WO L S → ℂ), IsModel ψ a₁ b M₁ →
    ∃ M₂ : (Matrix (Fin 1) n k → ℂ) →ₗ[ℂ] (WO S L'' → ℂ), IsModel ψ b a M₂ ∧
      ∀ f ∈ SB (n → k), hat p ψ ν f ∈ SB (n → k) ∧
        ∀ x : WO L S, M₂ (ofRow (hat p ψ ν f)) (beta S ζ₁ ζ x) = M₁ (ofCol f) x

def SeeSawFourier (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
  ∀ (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (ζ₁ : Fin L.rank → D.host.E) (ζ : Fin L''.rank → D.host.E), OppLines L L'' ζ₁ ζ →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure →
  ∀ (p : SplitPt D k) (n nA nT : Type) [Fintype n] [DecidableEq n] [Fintype nA] [DecidableEq nA] [Fintype nT]
    [DecidableEq nT] (b : Frame p S n) (bA : Frame p A nA) (b₀ : Frame p V₀ (nA ⊕ Fin 1)) (bT : Frame p T nT)
    (bX : Frame p X (nT ⊕ Fin 1)), IsSumFrame o ζ₁ bA b₀ → IsSumFrame o'' ζ bT bX →
  ∀ (M₁ : (Matrix n (nA ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (WO V₀ S → ℂ)) (M₂ : (Matrix nT n k → ℂ) →ₗ[ℂ] (WO S T → ℂ)),
    IsModel ψ b₀ b M₁ → IsModel ψ b bT M₂ →
    ∃ N : (Matrix n nA k → ℂ) →ₗ[ℂ] (Matrix (nT ⊕ Fin 1) n k → ℂ) →ₗ[ℂ] (WO A S × WO S X → ℂ),
      (∀ Θ ∈ SB (Matrix (nT ⊕ Fin 1) n k), ∀ w : WO S X,
        IsModel ψ bA b ((LinearMap.funLeft ℂ ℂ fun u : WO A S => (u, w)).comp (N.flip Θ))) ∧
      (∀ Ψ ∈ SB (Matrix n nA k), ∀ u : WO A S,
        IsModel ψ b bX ((LinearMap.funLeft ℂ ℂ fun w : WO S X => (u, w)).comp (N Ψ))) ∧
      ∀ f ∈ SB (n → k), hat p ψ ν f ∈ SB (n → k) ∧ ∀ Ψ ∈ SB (Matrix n nA k), ∀ Φ ∈ SB (Matrix nT n k),
        ∀ (u : WO A S) (x' : WO S T) (x : WO L S),
          N Ψ (tensRow Φ (hat p ψ ν f)) (u, (o''.resT S).symm (x', beta S ζ₁ ζ x)) =
            M₂ Φ x' * M₁ (tensCol Ψ f) ((o.resS S).symm (u, x))

section Checks

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

end Checks

end GlobalTheory.IndefiniteRowSideFullHecke.SeeSawLineFourier

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitModelToPlaceModel

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.LocFlat.CFac
open GlobalTheory.FinPl (SplitPt)
open GlobalTheory.IndefiniteRowSideFullHecke.SeeSawLineFourier (atW beta nrm OppLines IsLineFrame ofCol ofRow LineFourier SeeSawFourier)
open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastCompare

theorem map_mem_integer {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (φ : k →* k') (hφ : Continuous φ)
    {a : k} (ha : a ∈ 𝒪[k]) : φ a ∈ 𝒪[k'] := by
  by_contra h
  rw [Valuation.mem_integer_iff, not_le] at h
  have hK : IsCompact (φ '' (𝒪[k] : Set k)) := (isCompact_iff_compactSpace.2 (inferInstance : CompactSpace 𝒪[k])).image hφ
  haveI : MulArchimedean (ValueGroupWithZero k') := ValuativeRel.isRankLeOne_iff_mulArchimedean.1 inferInstance
  have h0 : valuation k' (φ a) ≠ 0 := (zero_lt_one.trans h).ne'
  have hU : ∀ n : ℕ, IsOpen {y : k' | valuation k' y < valuation k' (φ a) ^ n} := fun n => by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    refine Filter.mem_of_superset ((IsValuativeTopology.hasBasis_nhds y).mem_of_mem (i := Units.mk0 _ (pow_ne_zero n h0)) trivial) ?_
    intro z hz
    have := (valuation k').map_add_lt hz hy
    simpa using this
  obtain ⟨n, hn⟩ := hK.elim_directed_cover _ hU (fun y _ => by
      obtain ⟨n, hn⟩ := MulArchimedean.arch (valuation k' y) h
      exact Set.mem_iUnion.2 ⟨n + 1, hn.trans_lt (pow_lt_pow_right₀ h n.lt_succ_self)⟩)
    (directed_of_isDirected_le fun m n hmn y hy => lt_of_lt_of_le hy (pow_le_pow_right₀ h.le hmn))
  have := hn ⟨a ^ n, pow_mem ha n, rfl⟩
  simp at this

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {Y Y' n n' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype n] [DecidableEq n]
  [Fintype n'] [DecidableEq n']

variable {q : SplitPt D k} {S T : HSp D} {s : k} {σ : Y' ≃ n'} {σ' : Y ≃ n} {FS : Frame k S.rank Y'} {FT : Frame k T.rank Y}
  {α : GlobalTheory.FinPl.Frame q S n'} {β : GlobalTheory.FinPl.Frame q T n}

section Lines

variable {L L'' : HSp D} {ζ₁ : Fin L.rank → D.host.E} {ζ : Fin L''.rank → D.host.E}

end Lines

end GlobalTheory.LastCompare

end
end
end

-- Source module: PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.IwahoriSphericalTransfer

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompletionIso

open ValuativeRel

section Val

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem valuation_le_one_of_map (f : k ≃+* k') (hf : Continuous f) {x : k}
    (hx : valuation k' (f x) ≤ 1) : valuation k x ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have hx0 : x ≠ 0 := by rintro rfl; simp at h
  have h1 : valuation k x⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ h
  have h2 := GlobalTheory.TypeRec.TwistInert.valuation_lt_one_map f.toRingHom hf h1
  have hfx : f x ≠ 0 := (map_ne_zero f).2 hx0
  have hw : 0 < valuation k' (f x) := by rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 hfx
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_inv₀] at h2
  exact absurd ((inv_lt_one₀ hw).1 h2) (not_lt.2 hx)

theorem valuation_lt_one_of_map (f : k ≃+* k') (hf : Continuous f) {x : k}
    (hx : valuation k' (f x) < 1) : valuation k x < 1 := by
  by_contra h
  rw [not_lt] at h
  have hx0 : x ≠ 0 := by rintro rfl; simp at h
  have h1 : x⁻¹ ∈ 𝒪[k] := by
    rw [Valuation.mem_integer_iff, map_inv₀]; exact inv_le_one_of_one_le₀ h
  have h2 := GlobalTheory.LastCompare.map_mem_integer f.toMonoidHom hf h1
  rw [Valuation.mem_integer_iff] at h2
  have hfx : f x ≠ 0 := (map_ne_zero f).2 hx0
  have hw : 0 < valuation k' (f x) := by rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 hfx
  have h3 : valuation k' (f x⁻¹) ≤ 1 := h2
  rw [map_inv₀, map_inv₀] at h3
  exact absurd hx (not_lt.2 ((inv_le_one₀ hw).1 h3))

variable (f : k ≃+* k') (hf : Continuous f) {n : Type} [Fintype n] [DecidableEq n]

theorem map_map_symm (h : GL n k') :
    Matrix.GeneralLinearGroup.map f.toRingHom (Matrix.GeneralLinearGroup.map f.symm.toRingHom h) = h := by
  ext a b
  simp


include hf in
theorem map_symm_mem_KO {h : GL n k'} (hh : h ∈ GlobalTheory.SplitWeil.KO k' n) :
    Matrix.GeneralLinearGroup.map f.symm.toRingHom h ∈ GlobalTheory.SplitWeil.KO k n := by
  obtain ⟨h0, rfl⟩ := hh
  let j : 𝒪[k'] →+* 𝒪[k] := (f.symm.toRingHom.comp (algebraMap 𝒪[k'] k')).codRestrict 𝒪[k] (fun y => by
      show valuation k (f.symm (y : k')) ≤ 1
      apply valuation_le_one_of_map f hf
      rw [RingEquiv.apply_symm_apply]
      exact y.2)
  refine ⟨Matrix.GeneralLinearGroup.map j h0, ?_⟩
  ext a b
  simp [j] <;> rfl


include hf in
theorem map_symm_mem_iwahori [LinearOrder n] {h : GL n k'} (hh : h ∈ GlobalTheory.SmGL.iwahori k' n) :
    Matrix.GeneralLinearGroup.map f.symm.toRingHom h ∈ GlobalTheory.SmGL.iwahori k n := by
  rw [GlobalTheory.SmGL.mem_iwahori] at hh ⊢
  refine ⟨map_symm_mem_KO f hf hh.1, fun a b hab => ?_⟩
  apply valuation_lt_one_of_map f hf
  have := hh.2 a b hab
  simpa using this

end Val

theorem fixed_ne_bot_transfer {G G' V V' : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (ρ : Representation ℂ G V) (ρ' : Representation ℂ G' V') (φ : G →* G')
    (ψ : G' → G) (hψ : ∀ g, φ (ψ g) = g) (e : V ≃ₗ[ℂ] V') (he : ∀ g x, e (ρ g x) = ρ' (φ g) (e x))
    (H : Subgroup G) (H' : Subgroup G') (hH : ∀ h ∈ H', ψ h ∈ H) :
    GlobalTheory.PRep.fixed ρ H ≠ ⊥ → GlobalTheory.PRep.fixed ρ' H' ≠ ⊥ := by
  intro hne
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hx' : ∀ h : H, ρ (h : G) x = (((1 : H →* ℂˣ) h : ℂˣ) : ℂ) • x := hx
  refine (Submodule.ne_bot_iff _).2 ⟨e x, ?_, by simpa using hx0⟩
  show ∀ h : H', ρ' (h : G') (e x) = (((1 : H' →* ℂˣ) h : ℂˣ) : ℂ) • e x
  intro h
  have h1 := hx' ⟨ψ h, hH h h.2⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
  rw [← hψ h, ← he, h1]

theorem iwahori_spherical_transfer : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (i : v.adicCompletion F ≃+* w.adicCompletion K), Continuous i → ∀ (a : ℕ) (σ : SmIrr (GL (Fin a) (v.adicCompletion F))) (σ' : SmIrr (GL (Fin a) (w.adicCompletion K))) (e : σ.V ≃ₗ[ℂ] σ'.V), (∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)) → (GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SmGL.iwahori (v.adicCompletion F) (Fin a)) ≠ ⊥ → GlobalTheory.PRep.fixed σ'.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion K) (Fin a)) ≠ ⊥) ∧ (GlobalTheory.SmGL.IsSpherical σ.ρ → GlobalTheory.SmGL.IsSpherical σ'.ρ) := by
  intro F K _ _ _ _ v w i hi a σ σ' e he
  exact ⟨fixed_ne_bot_transfer σ.ρ σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom)
      (Matrix.GeneralLinearGroup.map i.symm.toRingHom) (map_map_symm i) e he _ _
      (fun h hh => map_symm_mem_iwahori i hi hh),
    fixed_ne_bot_transfer σ.ρ σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom)
      (Matrix.GeneralLinearGroup.map i.symm.toRingHom) (map_map_symm i) e he _ _
      (fun h hh => map_symm_mem_KO i hi hh)⟩

end GlobalTheory.CompletionIso
end
end
end
