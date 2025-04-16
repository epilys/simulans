from textual.logging import TextualHandler
from textual.screen import Screen
from textual.app import App, ComposeResult
from textual.widgets import Footer, Header, Static
from textual.containers import HorizontalGroup, VerticalScroll, Vertical, Container, Grid
from textual.widgets import Button, Digits, Footer, Header, Placeholder, Input, DataTable, Static, ContentSwitcher, Log, Label
from textual.reactive import reactive

import logging

class MemoryLogHandler(logging.Handler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
        self.setFormatter(formatter)
        self.log = []

    def emit(self, record):
        self.log.append(record)

logger = logging.getLogger(__name__)
logging.basicConfig(filename='debugger.log', encoding='utf-8', level=logging.DEBUG)
memory_log_handler = MemoryLogHandler()
logger.addHandler(memory_log_handler)

class MemoryTable(DataTable):
    def on_mount(self) -> None:
        self.table.add_columns("address", "value")
        self.table.add_rows([(hex(0x40000), hex(2)), (hex(0x40004), hex(2342))])

class Registers(Static):
    def __init__(self):
        self = Placeholder("registers")

class Memory(ContentSwitcher):
    def compose(self) -> ComposeResult:
        yield Placeholder("none loaded", id="none")
        yield Placeholder("loading", id="loading")
        yield Placeholder("l", id="loading")

class Prompt(Input):
    cursor_blink = reactive(True)

    def on_input_submitted(self,  event: Input.Submitted):
        logger.debug(str(event))
        self.clear()

class State(Vertical):
    REGISTER_COLUMNS = ("register", "value")

    table = DataTable(classes="register-table")

    def compose(self) -> ComposeResult:
        yield self.table
        yield Placeholder("memory contents placeholder", classes="box")

    def on_mount(self) -> None:
        self.table.add_columns(*State.REGISTER_COLUMNS)
        for i in range(0,32):
            self.table.add_row(f"x{i}", hex(2342))

class LogScreen(Screen):
    def __init__(self, *args, **kwargs):
        self.content = "\n".join([memory_log_handler.formatter.format(l) for l in memory_log_handler.log])
        super().__init__(*args, **kwargs)

    def compose(self) -> ComposeResult:
        log = Log()
        log.write(self.content)
        yield Grid(
            Label("Log", id="question"),
            log,
            Button("Quit", variant="error", id="quit"),
            id="dialog",
        )

    def on_button_pressed(self, event: Button.Pressed) -> None:
        if event.button.id == "quit":
            self.app.pop_screen()
            self.app.refresh_bindings()

class SimulansDebugger(App):
    """An interactive Simulans debugger."""

    CSS_PATH = "debugger.tcss"
    BINDINGS = [
            ("d", "toggle_dark", "Toggle dark mode"),
            ("l", "toggle_log", "Toggle log display"),
            ("s", "screenshot", ""),
            ("escape", "close", "close"),
            ]

    def compose(self) -> ComposeResult:
        """Create child widgets for the app."""
        yield Header()
        yield State(classes="vertical")
        yield Prompt(placeholder="Enter command", id="prompt", classes="prompt")
        yield Footer()

    def action_toggle_dark(self) -> None:
        """An action to toggle dark mode."""
        self.theme = (
            "textual-dark" if self.theme == "textual-light" else "textual-light"
        )

    def action_toggle_log(self) -> None:
        logger.debug("push_screen")
        self.push_screen(LogScreen())
        self.refresh_bindings()

    def action_close(self) -> None:
        logger.debug("close")
        if len(self.app.screen_stack) > 1:
            self.app.pop_screen()
            self.refresh_bindings()

    def action_screenshot(self) -> None:
        self.app.save_screenshot()

    def check_action(
        self, action: str, parameters: tuple[object, ...]
    ) -> bool | None:
        """Check if an action may run."""
        screen_no = len(self.app.screen_stack)
        if action == "close" and screen_no == 1:
            return False
        if action == "toggle_log" and screen_no > 1:
            return False
        return True


if __name__ == "__main__":
    app = SimulansDebugger()
    app.run()
