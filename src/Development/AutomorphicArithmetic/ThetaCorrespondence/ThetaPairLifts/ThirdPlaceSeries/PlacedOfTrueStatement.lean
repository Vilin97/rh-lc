module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedP
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIncAMulMemIntAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesAgreeAlmostEverywhere
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevTraceMemStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TraceChiStatement
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyProperty

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FamPlaced

section Prim

open GlobalTheory.FinPl

theorem incA_mul_mem_intAt {D : D7} (v : GlobalTheory.FinPl.Pl D) (c : D.host.E) (N : ℤ) (hint : IsIntegral ℤ (N • c))
    (hv : (N : 𝓞 D.host.F) ∉ v.asIdeal) {a : AE D} (ha : a ∈ intAt D (· = v)) : incA D c * a ∈ intAt D (· = v) := by
  have hN : N ≠ 0 := fun h => hv (by rw [h]; simp)
  have hNF : (N : D.host.F) ≠ 0 := Int.cast_ne_zero.2 hN
  refine ⟨Ideal.mul_mem_left _ _ ha.1, ?_⟩
  have hc : finPart D (incA D c) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c := rfl
  rw [map_mul, hc, ← AeUnit.idem_mul_finPart D v ha.1, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  refine GlobalTheory.HostAdeleIso.intAE_mul_mem D ?_ ha.2
  refine AddSubgroup.subset_closure ⟨_, AeUnit.inv_smul_singleV_mem v N hv, ⟨N • c, hint⟩, ?_⟩
  exact AeUnit.tmul_eq_inv_smul_tmul N hNF _ c

theorem prim_std {D : D7} (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (hL : ∀ x, x ∈ L ↔ ∀ i, IsIntegral ℤ (x i)) (v : GlobalTheory.FinPl.Pl D)
    (z : Fin S.rank → D.host.E) (hz : ∀ i, IsIntegral ℤ (z i)) (i₀ : Fin S.rank) (π' : D.host.E) (hπ' : IsIntegral ℤ π') (N : ℤ)
    (hπ : z i₀ * π' = (N : D.host.E)) (hv : (N : 𝓞 D.host.F) ∉ v.asIdeal) (a : AE D) (ha : a ∈ idAt D (· = v)) :
    a • ratV z ∈ GlobalTheory.FinPl.latV S L (· = v) ↔ a ∈ intAt D (· = v) := by
  have hL' : ∀ x : Fin S.rank → D.host.E, x ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = x i := fun x => by
    rw [hL x]
    exact ⟨fun h i => ⟨⟨x i, h i⟩, rfl⟩, fun h i => by obtain ⟨b, hb⟩ := h i; exact hb ▸ b.2⟩
  have hN : N ≠ 0 := fun h => hv (by rw [h]; simp)
  have hNE : (N : D.host.E) ≠ 0 := Int.cast_ne_zero.2 hN
  have hz0 : z i₀ ≠ 0 := fun h => hNE (by rw [← hπ, h, zero_mul])
  have h1 : ((1 : ℤ) : 𝓞 D.host.F) ∉ v.asIdeal := by
    rw [Int.cast_one]; exact fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  rw [GlobalTheory.FinPl.Model.mem_latV_std S L hL' v]
  constructor
  · intro h
    have hi : a * incA D (z i₀) ∈ intAt D (· = v) := h i₀
    have hint : IsIntegral ℤ (N • (z i₀)⁻¹) := by
      have : N • (z i₀)⁻¹ = π' := by
        rw [zsmul_eq_mul, ← hπ, mul_comm (z i₀), mul_assoc, mul_inv_cancel₀ hz0, mul_one]
      rw [this]; exact hπ'
    have h2 := incA_mul_mem_intAt v (z i₀)⁻¹ N hint hv hi
    rwa [mul_comm a, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hz0, map_one, one_mul] at h2
  · intro h i
    show a * incA D (z i) ∈ intAt D (· = v)
    rw [mul_comm]
    exact incA_mul_mem_intAt v (z i) 1 (by rw [one_smul]; exact hz i) h1 h

end Prim

end GlobalTheory.FamPlaced
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeEqBaseOffTwist

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem lattice_eq_base_off_twist_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ p, p ∉ a.v.tP → GlobalTheory.FinPl.latV ((I.rec7 l Z).sp.X 0) (a.g.x 0).L (· = p) = GlobalTheory.FinPl.latV ((I.rec7 l Z).sp.X 0) ((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Lb.map ((LinearEquiv.funCongrLeft (I.rec7 l Z).host.E (I.rec7 l Z).host.E (finCongr (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 (I.rec7 l Z).host.E))) (· = p) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr row col hc p hp
  obtain ⟨hs⟩ := hW.tr.std
  obtain ⟨k, hk⟩ := (hs u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hx := (hTr.pinX.xs 0 (Nat.zero_le _)).2.2
  have hlb := hk.lb ()
  have hTp : (((B.T u : ℕ) : ℤ) : 𝓞 (I.rec7 l Z).host.F) ∉ p.asIdeal := by
    intro h; apply hp; rw [(ha.tie row col).1.tP p]; exact_mod_cast h
  have hd : ((B.T u : ℕ) : ℤ) ≠ 0 := fun h => hTp (by rw [h]; simp)
  have h1 : ((1 : ℤ) : 𝓞 (I.rec7 l Z).host.F) ∉ p.asIdeal := by
    rw [Int.cast_one]; exact fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  set e := finCongr (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) with he
  have hpi : X.piT u ∣ ((B.T u : ℕ) : 𝓞 B.host.E) := by
    refine ⟨⟨B.host.conj (X.piT u : B.host.E), map_isIntegral_int (B.host.conj : B.host.E →+* B.host.E) (X.piT u).2⟩, ?_⟩
    apply RingOfIntegers.ext
    have := X.piT_norm u
    push_cast
    exact this.symm
  refine le_antisymm (GlobalTheory.FinPl.latV_le_of_int_smul _ _ _ ((B.T u : ℕ) : ℤ) hd ?_ p hTp)
    (GlobalTheory.FinPl.latV_le_of_int_smul _ _ _ 1 one_ne_zero ?_ p h1)
  · intro y hy
    have hyi : ∀ j, IsIntegral ℤ (y j) := (hx y).1 hy
    refine Submodule.mem_map.2 ⟨fun j => (((B.T u : ℕ) : ℤ) • y) (e.symm j), (hlb _).2 fun j => ?_, ?_⟩
    · refine ⟨((B.T u : ℕ) : 𝓞 B.host.E) * ⟨y (e.symm j), hyi _⟩, ?_, fun _ => dvd_mul_of_dvd_left hpi _⟩
      show (((B.T u : ℕ) : ℤ) • y) (e.symm j) = _
      rw [Pi.smul_apply, zsmul_eq_mul]
      push_cast
      rfl
    · funext i
      show (((B.T u : ℕ) : ℤ) • y) (e.symm (e i)) = _
      rw [Equiv.symm_apply_apply]
  · rintro _ ⟨x, hxm, rfl⟩
    rw [one_smul]
    refine (hx _).2 fun j => ?_
    obtain ⟨r, hr, -⟩ := (hlb x).1 hxm (e j)
    show IsIntegral ℤ (x (e j))
    rw [hr]; exact r.2
end GlobalTheory.Fam
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedOfTrue

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.FamPlaced
section Prim
open GlobalTheory.FinPl
end Prim
theorem placedP_of_allTrue : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → _root_.GlobalTheory.MiTop.PlacedConditions (a.fam row col) a.d.B := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hT' row col hc
  refine ⟨a.k, a.fld, a.val, a.top, a.loc, a.ι, a.v, a.o, a.n, a.G, a.pl, hc, ha.vis, (ha.tie row col).1, ha.shape, ha.gpin,
    (ha.tie row col).2, ?_, ?_⟩
  swap
  · intro p hp b hb
    have hx := (hT'.pinX.xs B.R.m le_rfl).2.2
    have hTp : (((B.T u : ℕ) : ℤ) : 𝓞 (I.rec7 l Z).host.F) ∉ p.asIdeal := by
      intro h; apply hp; rw [(ha.tie row col).1.tP p]; exact_mod_cast h
    have hpos : 0 < B.R.N B.R.m := B.R.N_pos _
    refine prim_std _ _ hx p _ (fun i => ?_)
      (Fin.cast (Formalism.L2.Forms.rankN (I.rec7 l Z) _ le_rfl).symm ⟨B.R.N B.R.m - 1, Nat.sub_lt hpos one_pos⟩)
      (B.host.conj (X.piT u : B.host.E)) (map_isIntegral_int (B.host.conj : B.host.E →+* B.host.E) (X.piT u).2)
      ((B.T u : ℕ) : ℤ) ?_ hTp b hb
    · refine (hT'.z0 i).symm ▸ ?_
      show IsIntegral ℤ (TC.z0 X u _)
      unfold TC.z0
      split_ifs
      · exact (X.piT u).2
      · exact isIntegral_zero
    · have h0 : TC.z0 X u ⟨B.R.N B.R.m - 1, Nat.sub_lt hpos one_pos⟩ = (X.piT u : B.host.E) :=
        if_pos (Nat.sub_add_cancel hpos)
      have h1 := (hT'.z0 (Fin.cast (Formalism.L2.Forms.rankN (I.rec7 l Z) _ le_rfl).symm
        ⟨B.R.N B.R.m - 1, Nat.sub_lt hpos one_pos⟩)).trans h0
      have h2 : (X.piT u : B.host.E) * B.host.conj (X.piT u : B.host.E) = (((B.T u : ℕ) : ℤ) : B.host.E) := by
        rw [Int.cast_natCast]; exact X.piT_norm u
      exact (congrArg (fun t : B.host.E => t * B.host.conj (X.piT u : B.host.E)) h1).trans h2
  letI : Field a.k := a.fld
  letI : ValuativeRel a.k := a.val
  letI : TopologicalSpace a.k := a.top
  letI : IsNonarchimedeanLocalField a.k := a.loc
  constructor
  · exact ha.bot.1
  · exact ha.bot.2.2.1
  · refine ⟨1, -(I.rec7 l Z).host.xi0 ^ ((I.rec7 l Z).R.m / 2), by simp, ?_, ?_⟩
    · intro r; rw [one_mul]; exact ha.bot.2.2.2 r
    · exact ha.norm.2
  · exact fun i => (ha.stdG i).2.2
  · exact _root_.GlobalTheory.Fam.lattice_eq_base_off_twist_alt W hA u a ha hT' row col hc
  · intro κ hκ y e
    exact ⟨_root_.GlobalTheory.T.true_geometry_local_data_alt W hA u a ha hT' row col hc κ hκ y e, _root_.GlobalTheory.T.true_geometry_reduction_level_alt W hA u a ha hT' row col hc κ hκ y e⟩
end GlobalTheory.FamPlaced
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedOfTrueStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.placed_p_of_true_geometry : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → _root_.GlobalTheory.MiTop.PlacedConditions (a.fam row col) a.d.B := by
  first | exact @_root_.GlobalTheory.FamPlaced.placedP_of_allTrue | exact _root_.GlobalTheory.FamPlaced.placedP_of_allTrue | (intros; apply _root_.GlobalTheory.FamPlaced.placedP_of_allTrue <;> assumption)
end
end
end
