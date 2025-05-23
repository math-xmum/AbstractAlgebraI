/- Utilities for interacting with LLMlean API endpoints. -/
import Lean
open Lean

namespace LLMlean


inductive APIKind : Type
  | Ollama
  | TogetherAI
  | OpenAI
  | Claude
  | DeepSeek
  deriving Inhabited, Repr


inductive PromptKind : Type
  | FewShot
  | Instruction
  | Detailed
  deriving Inhabited, Repr


structure API where
  model : String
  baseUrl : String
  kind : APIKind := APIKind.Ollama
  promptKind := PromptKind.FewShot
  key : String := ""
deriving Inhabited, Repr


structure GenerationOptionsOllama where
  temperature : Float := 0.7
  /-- Maximum number of tokens to generate. `-1` means no limit. -/
  num_predict : Int := 5000
deriving ToJson

structure GenerationOptions where
  temperature : Float := 0.7
  numSamples : Nat := 1
deriving ToJson

structure GenerationOptionsQed where
  temperature : Float := 0.7
  numSamples : Nat := 1
deriving ToJson

structure OllamaTacticGenerationRequest where
  model : String
  prompt : String
  options : GenerationOptionsOllama
  raw : Bool := false
  stream : Bool := false
deriving ToJson

structure OllamaQedRequest where
  model : String
  prompt : String
  options : GenerationOptionsOllama
  raw : Bool := false
  stream : Bool := false
deriving ToJson

structure OllamaResponse where
  response : String
deriving FromJson

structure OpenAIMessage where
  role : String
  content : String
deriving FromJson, ToJson


structure OpenAITacticGenerationRequest where
  model : String
  messages : List OpenAIMessage
  n : Nat := 5
  temperature : Float := 0.7
  max_tokens : Nat := 8192
  stream : Bool := false
deriving ToJson


structure OpenAIChoice where
  message : OpenAIMessage
deriving FromJson

structure OpenAIResponse where
  id : String
  choices : List OpenAIChoice
deriving FromJson


section Claude
structure ClaudeGenerationRequest where
  model : String
  messages : List OpenAIMessage
  temperature : Float := 0.7
  max_tokens : Nat := 10000
  stream : Bool := false
deriving ToJson


structure ClaudeMessage where
  type: String
  text: String
deriving FromJson, ToJson



structure ClaudeResponse where
  id : String
  type : String
  content: List ClaudeMessage
  stop_reason : String
deriving FromJson, ToJson

end Claude

def getPromptKind (stringArg: String) : PromptKind :=
  match stringArg with
  | "fewshot" => PromptKind.FewShot
  | "detailed" => PromptKind.Detailed
  | _ => PromptKind.Instruction

def getOllamaAPI : IO API := do
  let url        := (← IO.getEnv "LLMLEAN_ENDPOINT").getD "http://localhost:11434/api/generate"
  let model      := (← IO.getEnv "LLMLEAN_MODEL").getD "wellecks/ntpctx-llama3-8b"
  let promptKind := (← IO.getEnv "LLMLEAN_PROMPT").getD "instruction"
  let apiKey     := (← IO.getEnv "LLMLEAN_API_KEY").getD ""
  let api : API := {
    model := model,
    baseUrl := url,
    kind := APIKind.Ollama,
    promptKind := getPromptKind promptKind,
    key := apiKey
  }
  return api

def getTogetherAPI : IO API := do
  let url        := (← IO.getEnv "LLMLEAN_ENDPOINT").getD "https://api.together.xyz/v1/chat/completions"
  let model      := (← IO.getEnv "LLMLEAN_MODEL").getD "Qwen/Qwen2.5-72B-Instruct-Turbo"
  let promptKind := (← IO.getEnv "LLMLEAN_PROMPT").getD "detailed"
  let apiKey     := (← IO.getEnv "LLMLEAN_API_KEY").getD ""
  let api : API := {
    model := model,
    baseUrl := url,
    kind := APIKind.TogetherAI,
    promptKind := getPromptKind promptKind,
    key := apiKey
  }
  return api


def getOpenAIAPI : IO API := do
  let url        := (← IO.getEnv "LLMLEAN_ENDPOINT").getD "https://api.openai.com/v1/chat/completions"
  let model      := (← IO.getEnv "LLMLEAN_MODEL").getD "gpt-4o"
  let promptKind := (← IO.getEnv "LLMLEAN_PROMPT").getD "detailed"
  let apiKey     := (← IO.getEnv "LLMLEAN_API_KEY").getD ""
  let api : API := {
    model := model,
    baseUrl := url,
    kind := APIKind.OpenAI,
    promptKind := getPromptKind promptKind,
    key := apiKey
  }
  return api

def getDeepSeekAPI : IO API := do
  let url        := (← IO.getEnv "LLMLEAN_ENDPOINT").getD "https://api.deepseek.com/v1/chat/completions"
  let model      := (← IO.getEnv "LLMLEAN_MODEL").getD "deepseek-chat"
  let promptKind := (← IO.getEnv "LLMLEAN_PROMPT").getD "detailed"
  let apiKey     := (← IO.getEnv "LLMLEAN_API_KEY").getD ""
  let api : API := {
    model := model,
    baseUrl := url,
    kind := APIKind.DeepSeek,
    promptKind := getPromptKind promptKind,
    key := apiKey
  }
  return api

def getClaudeAPI : IO API := do
  let url        := (← IO.getEnv "LLMLEAN_ENDPOINT").getD "https://api.anthropic.com/v1/messages"
  let model      := (← IO.getEnv "LLMLEAN_MODEL").getD "claude-3-5-sonnet-20241022"
  let promptKind := (← IO.getEnv "LLMLEAN_PROMPT").getD "detailed"
  let apiKey     := (← IO.getEnv "LLMLEAN_API_KEY").getD ""
  let api : API := {
    model := model,
    baseUrl := url,
    kind := APIKind.Claude,
    promptKind := getPromptKind promptKind,
    key := apiKey
  }
  return api

def getAPI : IO API := do
  let apiKind  := (← IO.getEnv "LLMLEAN_API").getD "openai"
  match apiKind with
  | "ollama" => getOllamaAPI
  | "together" => getTogetherAPI
  | "deepseek" => getDeepSeekAPI
  | "claude" | "anthropic" => getClaudeAPI
  | _ => getOpenAIAPI

def API.getResponse (api : API) := match api.kind with
  | .Claude => ClaudeResponse
  | _ => OpenAIResponse

def buildCmdArgs (api : API)  (options : GenerationOptions) (prompt : String) : IO.Process.SpawnArgs :=
  match api.kind with
  | .Claude =>
    let req : ClaudeGenerationRequest := {
      model := api.model,
      messages := [
        {
          role := "user",
          content := prompt
        }
      ],
      temperature := options.temperature
    };
    {
    cmd := "curl"
    args := #[
      "-X", "POST", api.baseUrl,
      "-H", "accept: application/json",
      "-H", "Content-Type: application/json",
      "-H", "anthropic-version: 2023-06-01",
      "-H", "x-api-key: " ++ api.key,
      "-d", (toJson req).pretty UInt64.size]
    }
  | _ =>
    let req : OpenAITacticGenerationRequest := {
      model := api.model,
      messages := [
        {
          role := "user",
          content := prompt
        }
      ],
      n := 1,
      temperature := options.temperature
      };
    {
    cmd := "curl"
    args := #[
      "-X", "POST", api.baseUrl,
      "-H", "accept: application/json",
      "-H", "Content-Type: application/json",
      "-H", "Authorization: Bearer " ++ api.key,
      "-d", (toJson req).pretty UInt64.size]
    }

def post {α β : Type} [ToJson α] [FromJson β] (req : α) (url : String) (apiKey : String): IO β := do
  let out ← IO.Process.output {
    cmd := "curl"
    args := #[
      "-X", "POST", url,
      "-H", "x-api-key: " ++ apiKey,
      "-H", "accept: application/json",
      "-H", "Content-Type: application/json",
      "-H", "Authorization: Bearer " ++ apiKey,
      "-d", (toJson req).pretty UInt64.size]
  }
  if out.exitCode != 0 then
     throw $ IO.userError s!"Request failed. If running locally, ensure that ollama is running, and that the ollama server is up at `{url}`. If the ollama server is up at a different url, set LLMLEAN_URL to the proper url. If using a cloud API, ensure that LLMLEAN_API_KEY is set."
  let some json := Json.parse out.stdout |>.toOption
    | throw $ IO.userError out.stdout
  let some res := (fromJson? json : Except String β) |>.toOption
    | throw $ IO.userError out.stdout
  return res


def postPrompt {β : Type}  [FromJson β] (prompt : String)
(api :API) (options : GenerationOptions) : IO β := do
  let out ← IO.Process.output $ buildCmdArgs api options prompt
  if out.exitCode != 0 then
     throw $ IO.userError s!"Request failed. If running locally, ensure that ollama is running, and that the ollama server is up at `{api.baseUrl}`. If the ollama server is up at a different url, set LLMLEAN_URL to the proper url. If using a cloud API, ensure that LLMLEAN_API_KEY is set."
  let some json := Json.parse out.stdout |>.toOption
    | throw $ IO.userError out.stdout
  let some res := (fromJson? json : Except String β) |>.toOption
    | throw $ IO.userError out.stdout
  return res


def parseOpenAIResponse (res: OpenAIResponse) : Array String :=
  (res.choices.map fun x => x.message.content).toArray

/-
def tacticGenerationOpenAI
(prompts : List String)
(api : API) (options : GenerationOptions) : IO $ (String × Float) := do
  --let mut results : HashSet String := HashSet.empty
  let mut resstr : String := ""
  for prompt in prompts do
    let res := ← postPrompt prompt api options
    for result in (parseOpenAIResponse res ) do
      resstr := resstr ++ result

  let finalResults := (resstr,1.0)
  return finalResults
-/



def parseClaudeResponse (res: ClaudeResponse) : Array String :=
  (res.content.map fun x => x.text).toArray


def hintGeneration
(prompts : List String)
(api : API) (options : GenerationOptions) : IO $ (String × Float) := do
  --let mut results : HashSet String := HashSet.empty
  let mut resstr : String := ""
  for prompt in prompts do
    match api.kind with
    |.Claude =>
      let res : ClaudeResponse ← postPrompt prompt api options
      for result in (parseClaudeResponse res) do
        resstr := resstr ++ result
    | _ =>
      let res : OpenAIResponse ← postPrompt prompt api options
      for result in (parseOpenAIResponse res) do
        resstr := resstr ++ result

  let finalResults := (resstr,1.0)
  --(results.toArray.filter filterGeneration).map fun x => (x, 1.0)
  return finalResults
