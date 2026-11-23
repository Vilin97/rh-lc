module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPairSpaceLinearMapViaPartialFourierStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastColumnDatumTensorMemSchwartzBruhatStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineModelKappaTransformIsLocalModel
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelBoxProductOrthogonalSumTarget
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelRestrictedToLineSlice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositi
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowFourierOntoAndSpanTransformedLastRowStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceLocalModelsLinearSubspace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontriviaStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineModelKappaTransformIsLocalModelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lineModel_kappa_transform_isLocalModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (L S L'' : HSp D) (ζ : Fin L.rank → D.host.E) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), L''.rank = 1 → τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ (s : k) (z₀ : Fin L''.rank → k), s ≠ 0 → τ.map p.pr *ᵥ z₀ = (-(p.xi * s)) • (fun i => p.pr (ζ i)) → ∀ (n : Type) [Fintype n] [DecidableEq n] (FS : Frame k S.rank n) (FL : Frame k L.rank Unit), (∀ r, FL.β r () = s * p.pr (ζ r)) → ∀ TLS, p.IsModel ψ FL FS TLS → ∃ FL'' : Frame k L''.rank Unit, (∀ r, FL''.β r () = z₀ r) ∧ ∃ TL, p.IsModel ψ FS FL'' TL ∧ ∀ (c : SB (Matrix n Unit k)) (Φ : SB (Matrix Unit n k)), (∀ η, Φ.1 η = GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (η ())) → ∀ w, TL Φ w = TLS c (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * w)) := by
  first | exact @GlobalTheory.KappaModel.kappa_model | exact GlobalTheory.KappaModel.kappa_model | (intros; apply GlobalTheory.KappaModel.kappa_model <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelBoxProductOrthogonalSumTargetStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.local_model_box_product_orthogonal_sum_target : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S X T L'' : HSp D) (o'' : OrthDec X T L'') (n Z : Type) [Fintype n] [DecidableEq n] [Fintype Z] [DecidableEq Z] (FS : Frame k S.rank n) (FT : Frame k T.rank Z) (FL : Frame k L''.rank Unit) (FX : Frame k X.rank (Z ⊕ Unit)), FX.β = fromCols (o''.iA.map p.pr * FT.β) (o''.iB.map p.pr * FL.β) → ∀ T₂ TL, p.IsModel ψ FS FT T₂ → p.IsModel ψ FS FL TL → ∀ TX : SB (Matrix (Z ⊕ Unit) n k) →ₗ[ℂ] (WO S X → ℂ), (∀ (a : SB (Matrix Z n k)) (b : SB (Matrix Unit n k)) (Φ : SB (Matrix (Z ⊕ Unit) n k)), (∀ x, Φ.1 x = a.1 x.toRows₁ * b.1 x.toRows₂) → TX Φ = o''.boxT S (T₂ a) (TL b)) → p.IsModel ψ FS FX TX := by
  first | exact @GlobalTheory.LocMod.BoxModel.isModel_boxT | exact GlobalTheory.LocMod.BoxModel.isModel_boxT | (intros; apply GlobalTheory.LocMod.BoxModel.isModel_boxT <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelRestrictedToLineSliceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.local_model_restricted_to_line_slice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∃ FL : Frame k B.L.rank Unit, (∀ r, FL.β r () = s * p.pr (B.ζ r)) ∧ ∀ (Ξ : SB (Matrix n n' k)) (u₀ : WO B.A S), ∃ T', p.IsModel ψ FL FS T' ∧ ∀ (c : SB (Matrix n Unit k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ()))) → ∀ w, T' c w = T₀ Ψ ((B.o.resS S).symm (u₀, w)) := by
  first | exact @GlobalTheory.SliceLine.slice_line | exact GlobalTheory.SliceLine.slice_line | (intros; apply GlobalTheory.SliceLine.slice_line <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelSliceFirstSummand

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SliceLeft

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac GlobalTheory.SliceLine

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def boxL (c : SB (Matrix n Unit k)) : SB (Matrix n n' k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) where
  toFun Ξ := box Ξ c
  map_add' Ξ Ξ' := Subtype.ext (funext fun x => by simp [box, splitCols, add_mul])
  map_smul' a Ξ := Subtype.ext (funext fun x => by simp [box, splitCols]; ring)

theorem heis_slice_left {S A L T : HSp D} (d : OrthDec S A L) (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ)
    (u u' : WO A T) (w : WO L T) :
    heisO ψ S T ((d.resS T).symm (u', 0)) f ((d.resS T).symm (u, w)) =
      heisO ψ A T u' (fun u => f ((d.resS T).symm (u, w))) u := by
  simp only [heisO]
  rw [d.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

theorem isHalf_slice_left {S A L T : HSp D} (d : OrthDec S A L) {a : AE D} {y : WO A T} (hy : IsHalf a y) :
    IsHalf a ((d.resS T).symm (y, 0)) := by
  intro i j
  rw [resS_symm_apply, Matrix.zero_mul, add_zero, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc, hy i l]

end GlobalTheory.SliceLeft

namespace GlobalTheory.SliceLeft

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac GlobalTheory.SliceLine

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
variable {ρ : ℕ} {B : BesLev D ρ} {s : k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {FA : Frame k B.A.rank n'} {F₀ : Frame k B.V₀.rank (n' ⊕ Unit)} {FL : Frame k B.L.rank Unit}

theorem up_fromCols_left (h : p.IsCoreFrame B s FA F₀) (hL : ∀ r, FL.β r () = s * p.pr (B.ζ r)) {S : HSp D}
    (FS : Frame k S.rank n) (x : Matrix n n' k) :
    p.up F₀ FS (fromCols x 0) = (B.o.resS S).symm (p.up FA FS x, 0) := by
  have k1 : x * FA.γ * B.o.qA.map (p.π.comp (incA D)) * F₀.β = fromCols x (0 : Matrix n Unit k) := by
    rw [beta_eq p h hL, Matrix.mul_fromCols]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (B.o.qA.map _) (B.o.iA.map _), ← Matrix.map_mul, B.o.qA_iA,
      ← Matrix.mul_assoc (B.o.qA.map _) (B.o.iB.map _), ← Matrix.map_mul, B.o.qA_iB]
    simp [FA.γβ]
  have k2 : fromCols x (0 : Matrix n Unit k) * F₀.γ = x * FA.γ * B.o.qA.map (p.π.comp (incA D)) := by
    rw [← k1, Matrix.mul_assoc (x * FA.γ * B.o.qA.map (p.π.comp (incA D))) F₀.β F₀.γ, F₀.βγ, Matrix.mul_one]
  rw [resS_symm_apply, Matrix.zero_mul, add_zero]
  unfold Place.up
  rw [pA, map_ι_mul, rat_map_π]
  congr 1
  rw [Matrix.mul_assoc FS.β (fromCols x 0) F₀.γ, k2]
  simp only [Matrix.mul_assoc]

theorem resS_up_fst (h : p.IsCoreFrame B s FA F₀) (hL : ∀ r, FL.β r () = s * p.pr (B.ζ r)) {S : HSp D}
    (FS : Frame k S.rank n) (t : Matrix n (n' ⊕ Unit) k) :
    (B.o.resS S (p.up F₀ FS t)).1 = p.up FA FS t.toCols₁ := by
  have k1 : t * F₀.γ * B.o.iA.map (p.π.comp (incA D)) * FA.β = t.toCols₁ := by
    calc t * F₀.γ * B.o.iA.map (p.π.comp (incA D)) * FA.β
        = ((t * F₀.γ) * fromCols (B.o.iA.map (p.π.comp (incA D)) * FA.β)
            (B.o.iB.map (p.π.comp (incA D)) * FL.β)).toCols₁ := by
          rw [Matrix.mul_fromCols, toCols₁_fromCols, Matrix.mul_assoc (t * F₀.γ)]
      _ = ((t * F₀.γ) * F₀.β).toCols₁ := by rw [← beta_eq p h hL]
      _ = t.toCols₁ := by rw [Matrix.mul_assoc, F₀.γβ, Matrix.mul_one]
  have k2 : t * F₀.γ * B.o.iA.map (p.π.comp (incA D)) = t.toCols₁ * FA.γ := by
    rw [← k1, Matrix.mul_assoc (t * F₀.γ * B.o.iA.map (p.π.comp (incA D))) FA.β FA.γ, FA.βγ, Matrix.mul_one]
  rw [resS_apply]
  dsimp only
  unfold Place.up
  rw [jA, map_ι_mul, rat_map_π]
  simp only [Matrix.mul_assoc] at k2 ⊢
  rw [k2]

end GlobalTheory.SliceLeft

namespace GlobalTheory.SliceLeft

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac GlobalTheory.SliceLine

theorem toCols_add_left {k n n' : Type} [Field k] (t : Matrix n (n' ⊕ Unit) k) (x : Matrix n n' k) :
    (t + fromCols x (0 : Matrix n Unit k)).toCols₁ = t.toCols₁ + x ∧
      (t + fromCols x (0 : Matrix n Unit k)).toCols₂ = t.toCols₂ :=
  ⟨by ext i j; simp, by ext i j; simp⟩

theorem slice_left : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∀ (c : SB (Matrix n Unit k)) (w₀ : WO B.L S), ∃ T', p.IsModel ψ FA FS T' ∧ ∀ (Ξ : SB (Matrix n n' k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ()))) → ∀ u, T' Ξ u = T₀ Ψ ((B.o.resS S).symm (u, w₀)) := by
  intro D k _ _ _ _ p ψ ρ B S s n n' _ _ _ _ FA F₀ FS h T₀ hT c w₀
  obtain ⟨FL, hFL, -⟩ := slice_line D k p ψ ρ B S s n n' FA F₀ FS h T₀ hT
  let T' : SB (Matrix n n' k) →ₗ[ℂ] (WO B.A S → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (fun u : WO B.A S => (B.o.resS S).symm (u, w₀))).comp (T₀.comp (boxL c))
  have hT' : ∀ Ξ u, T' Ξ u = T₀ (box Ξ c) ((B.o.resS S).symm (u, w₀)) := fun _ _ => rfl
  refine ⟨T', ⟨fun Φ => ?_, fun x Φ Φ' hΦ => ?_, fun y hy Φ Φ' hΦ => ?_⟩, fun Ξ Ψ hΨ u => ?_⟩
  · exact GlobalTheory.BoxSlice.isThetaFunO_slice_left B.o (hT.theta (box Φ c)) w₀
  · have e := hT.trans (fromCols x 0) (box Φ c) (box Φ' c) (fun t => by
      rw [box_apply, box_apply, hΦ, (toCols_add_left t x).1, (toCols_add_left t x).2])
    funext u
    rw [hT', e, up_fromCols_left p h hFL, heis_slice_left]
    rfl
  · have e := hT.modul ((B.o.resS S).symm (y, 0)) (isHalf_slice_left B.o hy) (box Φ c) (box Φ' c) (fun t => by
      simp only [box_apply, hΦ, B.o.symplO_resS, AddEquiv.apply_symm_apply, resS_up_fst p h hFL, symplO_zero_right',
        add_zero]
      ring)
    funext u
    rw [hT', e, heis_slice_left]
    rfl
  · have e : Ψ = box Ξ c := Subtype.ext (funext fun x => by rw [hΨ, box_apply]; rfl)
    rw [hT', e]

end GlobalTheory.SliceLeft
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelSliceFirstSummandStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localModel_slice_firstSummand : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∀ (c : SB (Matrix n Unit k)) (w₀ : WO B.L S), ∃ T', p.IsModel ψ FA FS T' ∧ ∀ (Ξ : SB (Matrix n n' k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ()))) → ∀ u, T' Ξ u = T₀ Ψ ((B.o.resS S).symm (u, w₀)) := by
  first | exact @GlobalTheory.SliceLeft.slice_left | exact GlobalTheory.SliceLeft.slice_left | (intros; apply GlobalTheory.SliceLeft.slice_left <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceLocalModelsLinearSubspaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitLocalPlace_local_models_linear_subspace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y), p.IsModel ψ FS FT 0 ∧ ∀ T₁ T₂, p.IsModel ψ FS FT T₁ → p.IsModel ψ FS FT T₂ → p.IsModel ψ FS FT (T₁ + T₂) ∧ ∀ c : ℂ, p.IsModel ψ FS FT (c • T₁) := by
  first | exact @GlobalTheory.LocMod.Place.isModel_linear | exact GlobalTheory.LocMod.Place.isModel_linear | (intros; apply GlobalTheory.LocMod.Place.isModel_linear <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepKernelLocalModels

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastKerLoc


open GlobalTheory.LocFlat.CFac in
theorem lastLoc : ∀ (D : D7), LastLoc D := by
  intro D k _ _ _ _ _ _ p ν hν ψ hψ ψk hχ ρ B S X T L'' o'' τ hL hτ s z₀ hs hz n n' Z _ _ _ _ _ _ FA F₀ FS FT FX hcore hFX T₁ T₂ hT₁ hT₂
  classical
  obtain ⟨-, hck, -⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ hψ
  obtain ⟨hψc, hψ1⟩ := hck ψk hχ
  let κ : WO S L'' → WO B.L S := fun w => GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj B.L S ((rat τ : Mx D B.L.rank L''.rank) * w)
  let Bl : SB (Matrix Z n k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (WO B.A S → WO S X → ℂ) :=
    LinearMap.mk₂ ℂ (fun Ψ₂ Ψ₁ u => o''.boxT S (T₂ Ψ₂) fun w => T₁ Ψ₁ ((B.o.resS S).symm (u, κ w)))
      (by intros; funext u v; simp only [OrthDec.boxT, map_add (f := _), Pi.add_apply, add_mul])
      (by intros; funext u v; simp only [OrthDec.boxT, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc])
      (by intros; funext u v; simp only [OrthDec.boxT, map_add (f := _), Pi.add_apply, mul_add])
      (by intros; funext u v; simp only [OrthDec.boxT, map_smul, Pi.smul_apply, smul_eq_mul]; ring)
  obtain ⟨Λ, hΛ1, hΛ2⟩ := GlobalTheory.T.exists_pair_space_linear_map_via_partial_fourier k ν hν ψk hψc hψ1 n n' Z _ Bl
  obtain ⟨hXi, hPsi⟩ := GlobalTheory.T.last_column_datum_tensor_mem_schwartzBruhat k ν hν ψk hψc hψ1 n n' Z
  obtain ⟨hHat, hDec⟩ := GlobalTheory.T.row_fourier_onto_and_span_transformed_last_row k ν hν ψk hψc hψ1 n Z
  have hBl : ∀ a Ψ u v, Bl a Ψ u v = T₂ a (o''.resT S v).1 * T₁ Ψ ((B.o.resS S).symm (u, κ (o''.resT S v).2)) :=
    fun _ _ _ _ => rfl
  refine ⟨Λ, ⟨?_, ?_⟩, ?_⟩
  · intro Ξ₂ v
    obtain ⟨N, a, c, g, hg, hsum⟩ := hDec Ξ₂
    have hsl := fun i => GlobalTheory.T.localModel_slice_firstSummand D k p ψ ρ B S s n n' FA F₀ FS hcore T₁ hT₁ (c i) (κ (o''.resT S v).2)
    choose T' hT' hT'eq using hsl
    obtain ⟨hz0, hlin⟩ := GlobalTheory.T.splitLocalPlace_local_models_linear_subspace D k p ψ n n' B.A S FA FS
    refine ⟨∑ i, (T₂ (a i) (o''.resT S v).1) • T' i, ?_, ?_⟩
    · refine Finset.sum_induction _ (fun T => p.IsModel ψ FA FS T) (fun _ _ h1 h2 => (hlin _ _ h1 h2).1) hz0 ?_
      intro i _
      exact (hlin _ _ (hT' i) (hT' i)).2 _
    · intro Ξ₁ Ξ hΞ u
      have hΞs : Ξ = ∑ i, prodSB Ξ₁ (g i) := by
        apply Subtype.ext
        funext q
        rw [hΞ, Submodule.coe_sum, Finset.sum_apply, hsum, Submodule.coe_sum, Finset.sum_apply, Finset.mul_sum]
        rfl
      have hPi : ∀ i, ∃ Ψ₁ : SB (Matrix n (n' ⊕ Unit) k), ∀ x, Ψ₁.1 x = Ξ₁.1 x.toCols₁ * (c i).1 (Matrix.of fun r _ => x r (Sum.inr ())) :=
        fun i => hPsi Ξ₁ (c i)
      choose Ψ hΨ using hPi
      have hterm : ∀ i, Λ (prodSB Ξ₁ (g i)) = Bl (a i) (Ψ i) := fun i =>
        hΛ2 Ξ₁ (a i) (c i) (Ψ i) (prodSB Ξ₁ (g i)) (hΨ i) (fun q => by rw [prodSB_apply, hg])

      rw [hΞs, map_sum, Finset.sum_apply, Finset.sum_apply, LinearMap.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hterm, hBl, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hT'eq i Ξ₁ (Ψ i) (hΨ i) u]
  · intro Ξ₁ u
    obtain ⟨FL, hFL, hsl⟩ := GlobalTheory.T.local_model_restricted_to_line_slice D k p ψ ρ B S s n n' FA F₀ FS hcore T₁ hT₁
    obtain ⟨TLS, hTLS, hTLSeq⟩ := hsl Ξ₁ u
    obtain ⟨FL'', hFL'', TL, hTL, hTLeq⟩ := GlobalTheory.T.lineModel_kappa_transform_isLocalModel D k p ν hν ψ hψ ψk hχ B.L S L'' B.ζ τ hL hτ s z₀ hs hz n FS FL hFL TLS hTLS
    let P : SB (Matrix (Z ⊕ Unit) n k) →ₗ[ℂ] SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k) :=
      { toFun := fun g => prodSB Ξ₁ g
        map_add' := fun g g' => by apply Subtype.ext; funext q; simp [prodFn, mul_add]
        map_smul' := fun c g => by apply Subtype.ext; funext q; simp [prodFn]; ring }
    let TX : SB (Matrix (Z ⊕ Unit) n k) →ₗ[ℂ] (WO S X → ℂ) := LinearMap.proj u ∘ₗ Λ ∘ₗ P
    have hTXa : ∀ g, TX g = Λ (prodSB Ξ₁ g) u := fun _ => rfl
    refine ⟨TX, GlobalTheory.T.local_model_box_product_orthogonal_sum_target D k p ψ S X T L'' o'' n Z FS FT FL'' FX ?_ T₂ TL hT₂ hTL TX ?_, ?_⟩
    · rw [hFX]
      congr 1
      ext r j
      simp [Matrix.mul_apply, hFL'', Matrix.mulVec, dotProduct]
    · intro a b Φ hΦ
      obtain ⟨c, hc⟩ := hHat b
      obtain ⟨Ψ₁, hΨ₁⟩ := hPsi Ξ₁ c
      have h := hΛ2 Ξ₁ a c Ψ₁ (prodSB Ξ₁ Φ) hΨ₁ (fun q => by rw [prodSB_apply, hΦ, hc]; rfl)
      funext v
      rw [hTXa, h, hBl, OrthDec.boxT, hTLeq c b hc, hTLSeq c Ψ₁ hΨ₁]
    · intro Ξ₂ Ξ hΞ v
      have : Ξ = prodSB Ξ₁ Ξ₂ := Subtype.ext (funext hΞ)
      subst this
      rfl
  · intro Ψ₁ Ψ₂
    obtain ⟨Ξ, hΞ⟩ := hXi Ψ₁ Ψ₂
    refine ⟨Ξ, hΞ, fun u => ?_⟩
    rw [hΛ1 Ψ₁ Ψ₂ Ξ hΞ]
    rfl

end GlobalTheory.LastKerLoc

end
end
end
