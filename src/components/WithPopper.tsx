import PropTypes from "prop-types";
import React, {SyntheticEvent} from "react";
import {WithPopper} from "../interface";

const withPopper = ({children, relative, request}: WithPopper) => {
  const [anchorEl, setAnchorEl] = React.useState<EventTarget | null>(null);
  const [open, setOpen] = React.useState(false);
  const [placement, setPlacement] = React.useState<String | null>(null);
  const [pending, setPending] = React.useState(false);

  const handleClick = (newPlacement: String): Function => (event: SyntheticEvent<HTMLElement, Event>) => {
    event.persist();
    setAnchorEl(event.currentTarget);
    setPlacement(newPlacement);

    if (request) {

      if (open) {
        setOpen(false);
        setPending(false);
        return;
      }

      setPending(true);
      request().then(() => {
        setOpen(prev => placement !== newPlacement || !prev);
      }).catch(() => {
        setOpen(false);
      }).finally(() => {
        setPending(false);
      });

      return;
    }

    setOpen(prev => placement !== newPlacement || !prev);
  };

  const handleClose = () => {
    setOpen(false);
  };

  return (
    <>{relative
      ? <div className="relative">{children({open, anchorEl, pending, placement, handleClick, handleClose})}</div>
      : children({open, anchorEl, pending, placement, handleClick, handleClose})
    }</>
  );
};

export default withPopper;

withPopper.propTypes = {
  children: PropTypes.func.isRequired,
  relative: PropTypes.bool,
  request: PropTypes.func
};
