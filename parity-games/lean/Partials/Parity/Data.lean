import Partials.Parity.Model

/-! R7 literal historical diagnostic metadata, not an evaluated certificate.
The45 count describes a selected graph, never the47/48 original arenas. -/
namespace Partials.Parity.Data

def historicalSelectedCount : ℕ := 45
def historicalSelectedPriorities : List ℕ := [0, 4, 5, 12, 13, 16, 17]
def historicalReplayJSON : String := "{\"vertices_in_selected_graph\": 45, \"priority_alphabet_selected\": [0, 4, 5, 12, 13, 16, 17], \"profiles\": {\"forward_q2\": [[[\"s0\", 17]], [[\"s1\", 0]]], \"forward_q3\": [[[\"s0\", 17]], [[\"s1\", 0]]], \"post_q2\": [[[\"s0\", 17]], [[\"s1\", 0]]], \"post_q3\": [[\"bottom\"], [[\"s1\", 0]]]}, \"verdict\": \"forward joint-profile collision, distinct post-forget profiles\"}\n"

end Partials.Parity.Data
