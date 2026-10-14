import Partials.Arrival.Operational
import Partials.Arrival.Decoder
import Partials.Arrival.WrapperCounts

/-! Exact upper-graph embedding into the physical wrapper. Boundary departures
belong to the wrapper, so the successor correspondence is restricted to upper
nonsinks. The all-even aggregate decoder duty is stated with the actual scalar
decoder, rather than an arbitrary unnamed function. All source is uncompiled. -/
namespace Partials.Arrival

def upperEmbedding {k : ℕ} : UpperVertex k → Physical.Vertex k
  | .boundary o => .boundary o
  | .a i => .a i
  | .b i => .b i
  | .c i => .c i

theorem upperEmbedding_injective (k : ℕ) :
    Function.Injective (@upperEmbedding k) := by
  intro v w h
  cases v <;> cases w <;> simp_all [upperEmbedding]

theorem upperEmbedding_successor (hk : 3 ≤ k) (v : UpperVertex k)
    (hv : ¬ upperIsBoundary v) (slot : Fin 2) :
    upperEmbedding (upperSuccessor hk v slot) =
      Physical.next hk (upperEmbedding v) (decide (slot.val = 1)) := by
  cases v <;> simp_all only [upperIsBoundary, not_true_eq_false]
  all_goals fin_cases slot <;>
    simp [upperSuccessor, upperEmbedding, Physical.next, Physical.source]
  all_goals split_ifs <;> rfl

theorem upperInput_embedding (hk : 3 ≤ k) (port : InputPort) :
    upperEmbedding (upperInputVertex hk port) =
      (match port with | .E => Physical.source hk | .F => Physical.nearSource hk) := by
  cases port <;> rfl

theorem upper_boundary_is_cut_sink (o : NamedOutput) :
    upperIsBoundary (.boundary o : UpperVertex k) := by trivial

theorem physical_boundary_is_nonsink (o : NamedOutput) :
    ¬ Physical.IsSink (.boundary o : Physical.Vertex k) := by
  simp [Physical.IsSink]

def physicalAllEvenDecoderCounts (k : ℕ) (v : Batch) : NamedCounts :=
  namedBatchCounts k 0 v

/-- OPEN: cut a complete legal wrapper run into upper E/F excursions, apply
the operational decoder bridge, and recover exactly these boundary totals. -/
def PhysicalAllEvenDecoderDuty (hk : 3 ≤ k) : Prop :=
  Physical.UpperAggregateDecoderDuty hk (physicalAllEvenDecoderCounts k)

theorem physicalAllEvenDecoderCounts_total (k : ℕ) (v : Batch) :
    (physicalAllEvenDecoderCounts k v).total = v.total :=
  decoder_output_total k 0 v

end Partials.Arrival
