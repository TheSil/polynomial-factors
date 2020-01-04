report_enabled = True

class Proof:
    def __init__(self):
        self.msg = ""

    def report(self, level, msg):
        self.msg += level * " " + msg + "\n"

    def append(self, proof):
        self.msg += proof.msg

    def append_str(self, str):
        self.msg += str

    def print(self):
        global report_enabled
        if report_enabled:
            print(self.msg.rstrip())

