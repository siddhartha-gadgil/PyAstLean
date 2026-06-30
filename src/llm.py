import logging
import os

from dotenv import load_dotenv
from openai import OpenAI

load_dotenv()

logger = logging.getLogger(__name__)


def log_write(tag: str, message: str) -> None:
    """Lightweight query logger; visible under `--verbose` via the root logging config."""
    logger.debug("[%s] %s", tag, message)

provider_info = {
    "OpenAI": {
        "name": "OpenAI",
        "default_model": "o4-mini",
        "default_leanaide_model": "gpt-5.4",
        "api_key": os.getenv("OPENAI_API_KEY", "Key Not Found"),
        "models_url":"https://platform.openai.com/docs/models"
    },
    "Gemini": {
        "name": "Gemini",
        "default_model": "gemini-2.5-pro",
        "default_leanaide_model": "gemini-1.5-pro",
        "api_key": os.getenv("GEMINI_API_KEY", "Key Not Found"),
        "models_url": "https://developers.generativeai.google/models"
    },
    "OpenRouter": {
        "name": "OpenRouter",
        "default_model": "openai/gpt-5.4",
        "default_leanaide_model": "openai/gpt-5.4",
        "api_key": os.getenv("OPENROUTER_API_KEY", "Key Not Found"),
        "models_url": "https://openrouter.ai/models"
    },
    "DeepInfra": {
        "name": "DeepInfra",
        "default_model": "deepseek-ai/DeepSeek-R1-0528",
        "default_leanaide_model": "deepseek-ai/DeepSeek-R1-0528",
        "api_key": os.getenv("DEEPINFRA_API_KEY", "Key Not Found"),
        "models_url": "https://deepinfra.com/models"
    }
}

# Extract API keys for backwards compatibility
OPENAI_API_KEY = provider_info["OpenAI"]["api_key"]
GEMINI_API_KEY = provider_info["Gemini"]["api_key"]
OPENROUTER_API_KEY = provider_info["OpenRouter"]["api_key"]
DEEPINFRA_API_KEY = provider_info["DeepInfra"]["api_key"]

openai_client = OpenAI(api_key=OPENAI_API_KEY)
gemini_client = OpenAI(api_key=GEMINI_API_KEY, base_url="https://generativelanguage.googleapis.com/v1beta/openai/")
openrouter_client = OpenAI(api_key=OPENROUTER_API_KEY, base_url="https://openrouter.ai/api/v1")
deepinfra_client = OpenAI(api_key=DEEPINFRA_API_KEY, base_url="https://api.deepinfra.com/v1/openai")

# get prompt from docs/. Homedir is the repo root (parent of this src/ dir).
HOMEDIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DOCS_DIR = os.path.join(HOMEDIR, "docs")
CONTRACT_PROMPT_SYSTEM= os.path.join(DOCS_DIR, "contract-prompt-system.md")
VERIFIABLE_DESIGN_PROMPT = os.path.join(DOCS_DIR, "verifiable-python-design.md")

def match_provider_client(provider: str = "gemini"):
    provider = provider.lower()
    if provider == "openai":
        return openai_client
    elif provider == "gemini":
        return gemini_client
    elif provider == "openrouter":
        return openrouter_client
    elif provider == "deepinfra":
        return deepinfra_client
    else:
        return openai_client  # Default to OpenAI if provider is not recognized


def default_model_for(provider: str) -> str:
    """The default chat model for a provider name (case-insensitive), matching `provider_info`.
    Lets callers pass only a provider and get the right model without hard-coding one."""
    for key, info in provider_info.items():
        if key.lower() == provider.lower():
            return info["default_model"]
    return "gemini-2.5-pro"


## Get model list supported by API KEY
def get_supported_models(provider):
    """
    Get the list of models supported by the OpenAI API key.
    """
    client = match_provider_client(provider)
    try:
        models = client.models.list()
        return [model.id for model in models.data]
    except Exception as e:
        print(f"Error fetching models: {e}")
        return []

# print(get_supported_models("gemini"))

def model_response_gen(prompt:str, task:str = "", provider = "gemini", model:str ="gemini-2.5-pro", json_output: bool = False):
    """
    GPT response generator function.
    Args:
        prompt (str): The prompt to send to the GPT model.
        task (str): Optional system message to set the context for the model.
        model (str): The model to use for generating the response.
        provider (str): The provider to use for the model (e.g., "openai", "gemini", "openrouter", "deepinfra").
        json_output (bool): Request a JSON object response (`response_format={"type": "json_object"}`).
    """
    messages = []
    if task != "":
        messages.append({
            "role": "system",
            "content": task
        })
    messages.append({
        "role": "user",
        "content": prompt,
    })

    client = match_provider_client(provider)
    log_write("llm_query", f"provider={provider} model={model} json={json_output} prompt={prompt[:60]!r}...")
    create_kwargs = {"model": model, "messages": messages}
    if json_output:
        create_kwargs["response_format"] = {"type": "json_object"}
    response = client.chat.completions.create(**create_kwargs)
    if response is None:
        return "No response from model."

    return response.choices[0].message.content

def extract_python(code: str):
    """
    Extract Python code from a string that may contain code blocks.
    Args:
        code (str): The input string containing code blocks.
    """
    if code.startswith("```python"):
        code = code[len("```python"):]
    if code.startswith("```"):
        code = code[len("```"):]
    if code.endswith("```"):
        code = code[:-len("```")]
    return code.strip()

def contract_code(code: str, provider = "gemini", model=None):
    """
    Insert formal-method contracts (Requires/Ensures/Invariant/Assert/…) into a Python snippet.
    Args:
        code (str): The input Python code snippet.
        provider (str): The provider to use for the model (e.g., "openai", "gemini", "openrouter", "deepinfra").
        model (str): The model to use; defaults to the provider's default chat model.
    """
    model = model or default_model_for(provider)
    with open(CONTRACT_PROMPT_SYSTEM, 'r') as f:
        system_prompt = f.read()

    # The system prompt carries all the instructions and worked examples; the user turn is just the
    # program to annotate, fenced so the model returns the same shape.
    user_prompt = f"```python\n{code}\n```"

    response = model_response_gen(user_prompt, task=system_prompt, provider=provider, model=model)
    if response is None:
        return "No response from model."
    return extract_python(response)

def verifiable_design_code(code: str, provider = "gemini", model=None):
    """
    Restructure a Python snippet to maximise its provable surface, guided by the verifiable-design doc.
    Args:
        code (str): The input Python code snippet.
        provider (str): The provider to use for the model (e.g., "openai", "gemini", "openrouter", "deepinfra").
        model (str): The model to use; defaults to the provider's default chat model.
    """
    model = model or default_model_for(provider)
    with open(VERIFIABLE_DESIGN_PROMPT, 'r') as f:
        system_prompt = f.read()

    user_prompt = (
        "Rewrite the following Python program to maximise its provable surface per the design guide: "
        "keep each piece of math as a pure single-expression function, and push every print, input, "
        "raise, and try/except to the edge (a `main` entry point) so the math functions never read "
        "input, print, or raise. Preserve the program's observable behaviour. Output ONLY the rewritten "
        f"program in a single ```python code block.\n\n```python\n{code}\n```"
    )

    response = model_response_gen(user_prompt, task=system_prompt, provider=provider, model=model)
    if response is None:
        return "No response from model."
    return extract_python(response)