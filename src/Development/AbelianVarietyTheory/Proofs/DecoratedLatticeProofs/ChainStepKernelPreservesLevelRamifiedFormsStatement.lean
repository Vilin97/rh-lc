module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KmapEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DecoratedLatticePointMoveDiamond
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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KmapEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PolOfFnOfOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReferenceTupleOffPrimesEmpty
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SharpMemRange
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DecoratedPointMoveDiamondOperatorEq

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.DiaTheta

theorem decoratedPoint_move_diamondOperator_eq {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} (p : PtY ST SG Q y) (P : ST)
    (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) :
    p.mv (DecoSet.dia1 P a p.1.1.deco) = ⟨(⟨(DecoSet.dia1 P a p.1.1.deco, p.1.1.1.2), p.1.1.2⟩, p.1.2), p.2⟩ :=
  dif_pos ⟨p.1.1.2, p.2⟩

theorem xiAt_dia {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
    (u : Pr.Word) (i : ℕ) (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)) (p : PtAt R sel mu cst u i)
    (p' : PtAt R sel mu cst u (i + 1)) (P : Pr.vT u) (s : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) :
    xiAt Ch sel mu cst L u i b b' (p.mv (DecoSet.dia1 P s p.1.1.deco)) (p'.mv (DecoSet.dia1 P s p'.1.1.deco)) =
      xiAt Ch sel mu cst L u i b b' p p' := by
  rw [decoratedPoint_move_diamondOperator_eq, decoratedPoint_move_diamondOperator_eq]
  have hT := GlobalTheory.LvT.Built.levelPrimeDatum_diamond_invariant X.K p.1.1.deco p'.1.1.deco P s
  funext x
  unfold xiAt
  split_ifs with h1 h2 h3
  · unfold XiEntry
    exact congrArg (· * _) (congrFun hT x)
  · unfold XiCpl1
    exact congrArg (· * _) (congrFun hT x)
  · obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by have := R.two_le_m; omega⟩
    show xiOver Ch sel mu cst n h3 _ _ _ x = xiOver Ch sel mu cst n h3 _ _ _ x
    unfold xiOver
    exact congrArg (· * _) (congrFun hT x)
  · rfl

end GlobalTheory.DiaTheta

namespace GlobalTheory.DiaTheta

theorem th_dia : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Laws → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (b : (I.stp u a i).β) (b' : (I.stp u a (i + 1)).β) (p : (I.stp u a i).D b) (p' : (I.stp u a (i + 1)).D b') (P : (I.atIn u a).ST) (s : (Res P.1)ˣ), I.th u a i b b' (((I.atIn u a).A i).dia b P s p) (((I.atIn u a).A (i + 1)).dia b' P s p') = I.th u a i b b' p p' := by
  intro B X I _ u a i b b' p p' P s
  have e1 : ((I.atIn u a).A i).dia b P s p = PtY.mv p (DecoSet.dia1 P s p.1.1.deco) := rfl
  have e2 : ((I.atIn u a).A (i + 1)).dia b' P s p' = PtY.mv p' (DecoSet.dia1 P s p'.1.1.deco) := rfl
  rw [e1, e2]
  unfold TC.th thAt
  rw [xiAt_dia I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i b b' p p' P s, decoratedPoint_move_diamondOperator_eq, decoratedPoint_move_diamondOperator_eq]
  rfl

end GlobalTheory.DiaTheta
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelEntryRationalEquivarianceTransports

section

@[expose] public section

noncomputable section

namespace GlobalTheory.KerDia.Eqv

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem ent_smul : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ)
    {b : (I.stp u a i).β} {b' : (I.stp u a (i + 1)).β} (q : (I.stp u a i).D b) (q' : (I.stp u a (i + 1)).D b') (g : (I.stp u a i).G b)
    (g' : (I.stp u a (i + 1)).G b') (x : GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N i) → ℂ),
    (I.chain l u a).sharp i x ∈ LinearMap.range (fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 1) →
    ent I l u a i ((I.stp u a i).act b g q) ((I.stp u a (i + 1)).act b' g' q') ((I.stp u a i).tr B.fields.emb B.embLL b g x) =
      (I.stp u a (i + 1)).tr B.fields.emb B.embLL b' g' (ent I l u a i q q' x) := by
  intro B X I l h u a i b b' q q' g g' x hx
  obtain ⟨P, hP⟩ := hx
  funext y'
  have hP' : fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 1 P = fun y : GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N i) =>
      (∏ τ, deFr y τ ^ (I.chain l u a).sSharp i τ) * x y := hP
  have hr : I.rho u a i b ((I.stp u a i).act b g q) * I.rho' u a i b' ((I.stp u a (i + 1)).act b' g' q') ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
  have key := opOf_equiv B.fields.emb B.embLL ((I.chain l u a).sSharp i) ((I.chain l u a).sDiv i) I.J.cD (th_contDiff I h u a i q q')
    ((I.stp u a i).gam b g) ((I.stp u a (i + 1)).gam b' g') ((I.stp u a i).chr b g) ((I.stp u a (i + 1)).chr b' g') hr
    (th_move I l h u a i q q' g g') hP' y'
  refine (ent_apply I l u a i _ _ _ y').trans (key.trans ?_)
  rw [← ent_apply]
  rfl

end GlobalTheory.KerDia.Eqv
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelEntryRationalEquivarianceTransportsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem _root_.GlobalTheory.T.kernelEntry_rationalEquivariance_transports : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) {b : (I.stp u a i).β} {b' : (I.stp u a (i + 1)).β} (q : (I.stp u a i).D b) (q' : (I.stp u a (i + 1)).D b') (g : (I.stp u a i).G b) (g' : (I.stp u a (i + 1)).G b') (x : Fr B.fields.emb B.embLL (B.R.N i) → ℂ), (I.chain l u a).sharp i x ∈ LinearMap.range (fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 1) → ent I l u a i ((I.stp u a i).act b g q) ((I.stp u a (i + 1)).act b' g' q') ((I.stp u a i).tr B.fields.emb B.embLL b g x) = (I.stp u a (i + 1)).tr B.fields.emb B.embLL b' g' (ent I l u a i q q' x) := by
  first | exact @GlobalTheory.KerDia.Eqv.ent_smul | exact GlobalTheory.KerDia.Eqv.ent_smul | (intros; apply GlobalTheory.KerDia.Eqv.ent_smul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PointDeterminantDiamondOperatorInvariant

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section
namespace GlobalTheory.KerDia.RhoDia

section Gen
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pointDeterminant_diamondOperator_invariant {R : Ranks} (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) {n : ℕ}
    {ST SG Q : Finset (HeightOneSpectrum (𝓞 H.E))} (p q : DecoF H.E n ST SG Q) (P : ST) (c : (𝓞 H.E ⧸ P.1.asIdeal)ˣ)
    (hd : q.deco = DecoSet.dia1 P c p.deco) (hfr : q.fr = p.fr) : detPt H SQ q = detPt H SQ p := by
  have hN : q.deco.1.N = p.deco.1.N := by rw [hd]; rfl
  have hbe : q.deco.1.be = p.deco.1.be := by rw [hd]; rfl
  have h := ptFr_congr (p := q) (p' := p) hN hbe hfr
  unfold detPt ptIdl
  rw [h, hN]

end Gen

theorem rho_dia : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Laws → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (b : (I.stp u a i).β) (p : (I.stp u a i).D b) (b' : (I.stp u a (i + 1)).β) (p' : (I.stp u a (i + 1)).D b') (P : (I.atIn u a).ST) (s : (Res P.1)ˣ), I.rho u a i b (((I.atIn u a).A i).dia b P s p) = I.rho u a i b p ∧ I.rho' u a i b' (((I.atIn u a).A (i + 1)).dia b' P s p') = I.rho' u a i b' p' := by
  intro B X I _ u a i b p b' p' P s
  obtain ⟨h1, h2, -⟩ := GlobalTheory.LvT.Built.decoratedLatticePoint_move_diamond p P s
  obtain ⟨h1', h2', -⟩ := GlobalTheory.LvT.Built.decoratedLatticePoint_move_diamond p' P s
  have e := pointDeterminant_diamondOperator_invariant B.host I.SQ p.1.1 _ P s h1 h2
  have e' := pointDeterminant_diamondOperator_invariant B.host I.SQ p'.1.1 _ P s h1' h2'
  constructor
  · show ((rhoAt I.SQ I.C (I.xi a) i (p.mv (DecoSet.dia1 P s p.1.1.deco)).1.1 : ℂˣ) : ℂ) = ((rhoAt I.SQ I.C (I.xi a) i p.1.1 : ℂˣ) : ℂ)
    rw [rhoAt_eq, rhoAt_eq, e]
  · show ((rhoAt' I.SQ I.C (I.xi a) i (p'.mv (DecoSet.dia1 P s p'.1.1.deco)).1.1 : ℂˣ) : ℂ) = ((rhoAt' I.SQ I.C (I.xi a) i p'.1.1 : ℂˣ) : ℂ)
    rw [rhoAt'_eq, rhoAt'_eq, e']

end GlobalTheory.KerDia.RhoDia
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepKernelPreservesLevelRamifiedForms

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.KRamT

open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia

section Entry
attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre}

theorem tr_one {E K ι : Type} [Field E] [NumberField E] [Field K] [Fintype ι] {n : ℕ} (S : GStep E K n)
    (emb : ι → E →+* K) (σ : K →+* ℂ) (b : S.β) (F : Fr emb σ n → ℂ) : S.tr emb σ b 1 F = F := by
  funext y
  simp only [GStep.tr, map_one, trFr_apply, inv_one, Units.val_one, map_one, one_mul]
  exact congrArg F (frMul_one emb σ y)

theorem ent_dia (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) {b : (I.stp u a i).β}
    {b' : (I.stp u a (i + 1)).β} (p : (I.stp u a i).D b) (p' : (I.stp u a (i + 1)).D b') (P : (I.atIn u a).ST) (s : (Res P.1)ˣ) :
    ent I l u a i (((I.atIn u a).A i).dia b P s p) (((I.atIn u a).A (i + 1)).dia b' P s p') = ent I l u a i p p' := by
  unfold ent
  rw [(GlobalTheory.KerDia.RhoDia.rho_dia I l u a i b p b' p' P s).1, (GlobalTheory.KerDia.RhoDia.rho_dia I l u a i b p b' p' P s).2,
    GlobalTheory.DiaTheta.th_dia I l u a i b b' p p' P s]

theorem Kmap_stab (I : TC B X) (l : I.Laws) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m)
    (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) (g : (I.stp u a (i + 1)).Stab c')
    (f : Fr B.fields.emb B.embLL (B.R.N i) → ℂ) (hf : f ∈ ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i)) :
    (I.stp u a (i + 1)).tr B.fields.emb B.embLL c'.1 g.1 ((I.chain l u a).Kmap i c c' f) = (I.chain l u a).Kmap i c c' f := by
  rw [GlobalTheory.KerDia.Kmap_eq]
  have e3 := GlobalTheory.T.kernelEntry_rationalEquivariance_transports I l hI u a i ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') 1 g.1 f
    (GlobalTheory.KerDia.sharp_mem_range I l u a i hi f hf)
  have hg : (I.stp u a (i + 1)).act c'.1 g.1 ((I.stp u a (i + 1)).rep c') = (I.stp u a (i + 1)).rep c' := g.2
  have h1 : (I.stp u a i).act c.1 1 ((I.stp u a i).rep c) = (I.stp u a i).rep c :=
    @one_smul _ _ _ (GStep.actD _ c.1) _
  rw [h1, hg, tr_one] at e3
  exact e3.symm

theorem K_mem_Fi (I : TC B X) (l : I.Laws) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m) :
    ∀ φ ∈ (I.stp u a i).Fi B.fields.emb B.embLL (lamT (B.hcW u) i),
      (I.chain l u a).K i φ ∈ (I.stp u a (i + 1)).Fi B.fields.emb B.embLL (lamT (B.hcW u) (i + 1)) := by
  intro φ hφ c'
  let _ := (I.chain l u a).clsFin i
  have hK : (I.chain l u a).K i φ c' = ∑ c, (I.chain l u a).wt i c • (I.chain l u a).Kmap i c c' (φ c) := rfl
  rw [hK]
  refine ⟨Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _
    (GlobalTheory.AdForm.Keep.kmap_val I l u a i hi c c' _ (hφ c).1), fun g => ?_⟩

  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, Kmap_stab I l hI u a i hi c c' g _ (hφ c).1]

end Entry
end GlobalTheory.KRamT

namespace GlobalTheory.KRamT

open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia

section Dia
attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre}

theorem entry_dia (I : TC B X) (l : I.Laws) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m)
    (φ : ColT I l u a i) (hφ : φ ∈ (I.fm l u a).Fi i) (v : (I.atT l u a).vT) (s : ((I.atT l u a).Fv v)ˣ)
    (L : (I.chain l u a).cls i) (c' : (I.chain l u a).cls (i + 1)) :
    (I.fm l u a).dilT (i + 1) v s c' ((I.chain l u a).Kmap i ((I.fm l u a).dil i v s L) ((I.fm l u a).dil (i + 1) v s c')
      (φ ((I.fm l u a).dil i v s L))) =
    (I.chain l u a).Kmap i L c' ((I.fm l u a).dilT i v s L (φ ((I.fm l u a).dil i v s L))) := by
  have hφ' : φ ∈ (I.stp u a i).Fi B.fields.emb B.embLL (lamT (B.hcW u) i) := hφ
  change (I.atIn u a).dilT B.fields.emb B.embLL (i + 1) v s c'
      ((I.chain l u a).Kmap i ((I.atIn u a).dil i v s L) ((I.atIn u a).dil (i + 1) v s c')
        (φ ((I.atIn u a).dil i v s L))) =
    (I.chain l u a).Kmap i L c' ((I.atIn u a).dilT B.fields.emb B.embLL i v s L (φ ((I.atIn u a).dil i v s L)))
  have hx : φ ((I.atIn u a).dil i v s L) ∈ ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i) :=
    (hφ' ((I.atIn u a).dil i v s L)).1
  rw [Kmap_eq I l u a i _ _, Kmap_eq I l u a i L c']
  unfold AtIn.dilT AtIn.dil GStep.trTo
  have e1 := (I.stp u a i).mv_smul L.1 (((I.atIn u a).A i).diaPt v s L)
  have e2 := (I.stp u a (i + 1)).mv_smul c'.1 (((I.atIn u a).A (i + 1)).diaPt v s c')
  have e3 := GlobalTheory.T.kernelEntry_rationalEquivariance_transports I l hI u a i
    ((I.stp u a i).rep ((I.stp u a i).cl L.1 (((I.atIn u a).A i).diaPt v s L)))
    ((I.stp u a (i + 1)).rep ((I.stp u a (i + 1)).cl c'.1 (((I.atIn u a).A (i + 1)).diaPt v s c')))
    ((I.stp u a i).mv L.1 (((I.atIn u a).A i).diaPt v s L))
    ((I.stp u a (i + 1)).mv c'.1 (((I.atIn u a).A (i + 1)).diaPt v s c')) _
    (GlobalTheory.KerDia.sharp_mem_range I l u a i hi _ hx)
  unfold GStep.act at e3
  rw [e1, e2] at e3
  refine Eq.trans e3.symm ?_
  exact LinearMap.congr_fun (ent_dia I l u a i ((I.stp u a i).rep L) ((I.stp u a (i + 1)).rep c') v s) _

def dilEquiv (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (v : (I.atT l u a).vT) (s : ((I.atT l u a).Fv v)ˣ) :
    (I.chain l u a).cls i ≃ (I.chain l u a).cls i where
  toFun := (I.fm l u a).dil i v s
  invFun := (I.fm l u a).dil i v s⁻¹
  left_inv c := by rw [← (I.fm l u a).dil_mul, inv_mul_cancel, (I.fm l u a).dil_one]
  right_inv c := by rw [← (I.fm l u a).dil_mul, mul_inv_cancel, (I.fm l u a).dil_one]

theorem dia_K_eq (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (v : (I.atT l u a).vT) (s : ((I.atT l u a).Fv v)ˣ)
    (φ : ColT I l u a i) (c' : (I.chain l u a).cls (i + 1)) :
    (I.fm l u a).dilT (i + 1) v s c' ((I.chain l u a).K i φ ((I.fm l u a).dil (i + 1) v s c')) =
      ∑ L ∈ @Finset.univ _ ((I.chain l u a).clsFin i), (I.chain l u a).wt i L • (I.fm l u a).dilT (i + 1) v s c'
        ((I.chain l u a).Kmap i ((I.fm l u a).dil i v s L) ((I.fm l u a).dil (i + 1) v s c') (φ ((I.fm l u a).dil i v s L))) := by
  letI := (I.chain l u a).clsFin i

  simp only [ColumnChain.K, Formalism.ThetaLiftIndependence.kerOpM, map_sum, map_smul]
  refine (Equiv.sum_comp (dilEquiv I l u a i v s) _).symm.trans (Finset.sum_congr rfl fun L _ => ?_)
  have h : (I.chain l u a).wt i ((I.fm l u a).dil i v s L) = (I.chain l u a).wt i L := by
    unfold ColumnChain.wt
    rw [(I.fm l u a).dil_stab]
  show (I.chain l u a).wt i ((I.fm l u a).dil i v s L) • _ = _
  rw [h]
  rfl

end Dia

theorem kernel_keeps_ramT : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ φ : ColT I l u a i, RamT i φ → RamT (i + 1) ((I.chain l u a).K i φ) := by
  intro B X I hI _ l _ u a i hi φ hR
  letI := (I.chain l u a).clsFin i
  refine ⟨K_mem_Fi I l hI u a i hi φ hR.1, fun v c' => ?_⟩
  letI := (I.atT l u a).FvFin v
  letI := (I.atT l u a).FvDec v
  have hsum : ∑ s : ((I.atT l u a).Fv v)ˣ,
      (fun L => (I.fm l u a).dilT i v s L (φ ((I.fm l u a).dil i v s L))) = 0 := by
    funext L
    rw [Finset.sum_apply, ← finsum_eq_sum_of_fintype]
    exact hR.2 v L
  have hterm : ∀ s : ((I.atT l u a).Fv v)ˣ,
      (I.fm l u a).dilT (i + 1) v s c' ((I.chain l u a).K i φ ((I.fm l u a).dil (i + 1) v s c')) =
        (I.chain l u a).Klin i (fun L => (I.fm l u a).dilT i v s L (φ ((I.fm l u a).dil i v s L))) c' := by
    intro s
    refine (dia_K_eq I l u a i v s φ c').trans ?_
    show _ = ∑ L, (I.chain l u a).wt i L • (I.chain l u a).Kmap i L c'
      ((I.fm l u a).dilT i v s L (φ ((I.fm l u a).dil i v s L)))
    exact Finset.sum_congr rfl fun L _ => congrArg ((I.chain l u a).wt i L • ·)
      (entry_dia I l hI u a i hi φ hR.1 v s L c')
  rw [finsum_eq_sum_of_fintype]
  simp only [hterm]

  rw [← Finset.sum_apply, ← map_sum, hsum, map_zero]
  rfl

end GlobalTheory.KRamT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepKernelPreservesLevelRamifiedFormsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.chainStepKernel_preserves_levelRamifiedForms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ φ : ColT I l u a i, RamT i φ → RamT (i + 1) ((I.chain l u a).K i φ) := by
  first | exact @GlobalTheory.KRamT.kernel_keeps_ramT | exact GlobalTheory.KRamT.kernel_keeps_ramT | (intros; apply GlobalTheory.KRamT.kernel_keeps_ramT <;> assumption)
end
end
