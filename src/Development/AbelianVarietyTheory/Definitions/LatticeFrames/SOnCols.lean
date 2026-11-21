module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7} {c : Comm D} {ρ : RealD c} {t : Tup c} (A : ClsK ρ t)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} (o : TDat c k ι)

def SOnCols (D : D7) : Prop :=
  ∀ (c : Comm D) (ρ : RealD c) (t : Tup c) (A : ClsK ρ t) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → ρ.Is → A.Forms →
    o.I.Nodup → (∀ i, i ∈ o.I) → (Function.Injective fun i => (o.p i).v) → A.LevT o → A.FullT o →
    ∃ S : ∀ j, (ι → 𝓀[k]ˣ) → t.Col j → t.Col j, ∀ j, j ≤ D.R.m → ∀ η, ∀ ψ ∈ t.Ram j,
      S j η ψ ∈ t.Ram j ∧ ∀ β y, t.rd j β (S j η ψ) y = o.S (fun _ => η) j (t.rd j β ψ y)

def RamIff (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S : HSp D) (β : Frame p S n) (P : Pair k n)
    (g : 𝓀[k]ˣ → GL n k), (∀ s, g s • P = s • P) → ∀ φ : GA D S → ℂ,
      RamAt β P φ ↔ IsContAut S φ ∧ (∀ x, x • P = P → rTrans (β.gl x) φ = φ) ∧ ∑ᶠ s, rTrans (β.gl (g s)) φ = 0

end GlobalTheory.SeeSaw

end
